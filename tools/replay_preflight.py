#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Disk and isolation guard for `make verify-all` (docs/lessons.md, rule 7). Stdlib only, Linux /proc, read-only
except for the log it is asked to write.

The invariant is that a replay never dies on a full disk and never shares the machine with another Lean process
(lessons 21, 28, 32). A fixed number of free gigabytes does not express it: what a replay needs is the part of its
footprint that is not on disk yet, plus a margin.

  check [REPO]        exit 0 iff free space >= max(0, FOOTPRINT - size of REPO/build) + MARGIN; otherwise exit 1 and
                      say what to delete (the regenerable exports under build/, which git ignores)
  watch PID LOG       once a minute, until PID ends: append to LOG the free space and every process of the Lean
                      family that does not descend from PID. Below ABORT free bytes: log it and send SIGTERM to
                      PID's process group (a replay that would die anyway is stopped while its log is intact)
  --self-test

FOOTPRINT is the measured size of build/ after a full replay plus the largest dip of free space during it; the
record that it was measured from is named beside the constant. Re-measure when the replay grows.
"""
import os
import signal
import sys
import time

GB = 1 << 30
FOOTPRINT = 6 * GB   # build/ held 5371830436 bytes when the run below died in its comparator step; rounded up
MEASURED_FROM = "docs/replay/2026-11-16-session13-PA-KL-partial.txt"
MARGIN = 5 * GB
ABORT = 3 * GB
FAMILY = {"lean", "lake", "leanchecker", "leanchecker-par", "leanchecker-paranoid", "nanoda_bin", "lean4lean",
          "con-leche", "con-ron", "leanexport"}


def tree_size(path):
    total = 0
    for root, _, files in os.walk(path):
        for f in files:
            try:
                total += os.lstat(os.path.join(root, f)).st_size
            except OSError:
                pass
    return total


def needed(build_size, footprint=FOOTPRINT, margin=MARGIN):
    return max(0, footprint - build_size) + margin


def free_bytes(path):
    st = os.statvfs(path)
    return st.f_bavail * st.f_frsize


def check(repo):
    build = tree_size(os.path.join(repo, "build"))
    free, need = free_bytes(repo), needed(build)
    line = (f"replay-preflight: free {free / GB:.1f} GB; build/ holds {build / GB:.1f} GB of a {FOOTPRINT / GB:.1f} GB "
            f"footprint (measured: {MEASURED_FROM}); needed {need / GB:.1f} GB including a {MARGIN / GB:.0f} GB margin")
    if free >= need:
        print(line + ": OK")
        return 0
    print(line + ": NOT ENOUGH. Delete regenerable outputs that git ignores (build/challenge, build/commit, "
                 "cargo target directories, stale scratch) and run again; do not start the replay.")
    return 1


def foreign(procs, root):
    """procs: {pid: (ppid, name)}. Lean-family processes that do not descend from root."""
    out = []
    for pid, (_, name) in sorted(procs.items()):
        if name not in FAMILY:
            continue
        p, seen = pid, set()
        while p in procs and p != root and p not in seen:
            seen.add(p)
            p = procs[p][0]
        if p != root:
            out.append((pid, name))
    return out


def read_procs():
    procs = {}
    for d in os.listdir("/proc"):
        if d.isdigit():
            try:
                with open(f"/proc/{d}/stat") as fh:
                    s = fh.read()
                name = s[s.index("(") + 1:s.rindex(")")]
                procs[int(d)] = (int(s[s.rindex(")") + 2:].split()[1]), name)
            except (OSError, ValueError):
                pass
    return procs


def stamp():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def watch(pid, log, path=".", interval=60):
    while True:
        try:
            os.kill(pid, 0)
        except OSError:
            break
        free = free_bytes(path)
        f = foreign(read_procs(), pid)
        names = "".join(f" {n}:{p}" for p, n in f)
        with open(log, "a") as fh:
            fh.write(f"{stamp()} {len(f)} foreign Lean process(es){names}; free {free} bytes ({free / GB:.2f} GB)\n")
            if free < ABORT:
                fh.write(f"{stamp()} ABORT: free space below {ABORT / GB:.0f} GB; SIGTERM to the process group of {pid}\n")
        if free < ABORT:
            try:
                os.killpg(os.getpgid(pid), signal.SIGTERM)
            except OSError:
                pass
            return 2
        time.sleep(interval)
    with open(log, "a") as fh:
        fh.write(f"{stamp()} process {pid} has ended\n")
    return 0


def self_test():
    results = []
    results.append(("nothing on disk yet: the whole footprint plus the margin", needed(0, 5 * GB, 5 * GB) == 10 * GB))
    results.append(("exports already on disk: only the margin", needed(6 * GB, 5 * GB, 5 * GB) == 5 * GB))
    results.append(("a partly built tree: the rest plus the margin", needed(2 * GB, 5 * GB, 5 * GB) == 8 * GB))
    procs = {1: (0, "init"), 10: (1, "bash"), 11: (10, "make"), 12: (11, "lean"), 13: (12, "leanchecker"),
             20: (1, "bash"), 21: (20, "lean"), 30: (1, "python3"), 31: (30, "nanoda_bin"), 40: (1, "lake")}
    results.append(("descendants of the replay are not foreign; others of the family are",
                    foreign(procs, 10) == [(21, "lean"), (31, "nanoda_bin"), (40, "lake")]))
    results.append(("a process outside the family is never listed", all(n in FAMILY for _, n in foreign(procs, 1))))
    results.append(("with the replay as init's child, a sibling shell's Lean is foreign",
                    (21, "lean") in foreign(procs, 11)))
    for name, ok in results:
        print(f"replay-preflight self-test: {'PASS' if ok else 'FAIL'}: {name}")
    return all(ok for _, ok in results)


if __name__ == "__main__":
    a = sys.argv[1:]
    if "--self-test" in a:
        sys.exit(0 if self_test() else 1)
    if a[:1] == ["watch"] and len(a) == 3:
        sys.exit(watch(int(a[1]), a[2]))
    if a[:1] == ["check"]:
        sys.exit(check(a[1] if len(a) > 1 else "."))
    print(__doc__)
    sys.exit(2)
