#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""Attribution blocks on records (owner decision 2026-11-19, docs/decisions/2026-11-19-attribution-blocks.md).

Records (review answers, replay records, session logs, pre-registrations, decision memos, release notes, result
files) are never edited. The one exception: a fixed attribution block appended at the end, so that a record copied
out of the repository still names its author and licence. This tool appends the block and proves that nothing else
changed.

  add LIST          append the block to every file named in LIST (one path per line); refuse a file that already
                    ends with a block; print "<path> <sha256 before> <sha256 after> <licence>" per file
  verify BASE HEAD RECORD
                    for every line of RECORD: the file at commit HEAD must be, byte for byte, the file at commit
                    BASE followed by the block for its type and licence, and both hashes must be the recorded ones.
                    Exit 1 on the first difference. HEAD may be "." for the working tree.
  --self-test

The block for a Markdown file is an HTML comment; for a text file, three lines starting with "# ". Licence: the one
REUSE.toml assigns to the path (CC-BY-4.0 for docs/ and review/, Apache-2.0 for results and test records).
"""
import hashlib
import subprocess
import sys

OWNER = "2026 Thomas Falk III <research@thomas-falk-research.com>"


def licence(path):
    return "CC-BY-4.0" if path.startswith(("docs/", "review/")) else "Apache-2.0"


def block(path):
    lic = licence(path)
    if path.endswith(".md"):
        return ("\n<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.\n"
                f"SPDX-FileCopyrightText: {OWNER}\nSPDX-License-Identifier: {lic} -->\n").encode()
    return ("\n# Attribution, appended 2026-11-19 by owner decision; the lines above are the record as written.\n"
            f"# SPDX-FileCopyrightText: {OWNER}\n# SPDX-License-Identifier: {lic}\n").encode()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def add(list_path):
    for path in [l.strip() for l in open(list_path) if l.strip()]:
        data = open(path, "rb").read()
        blk = block(path)
        if data.endswith(blk) or b"SPDX-FileCopyrightText" in data[-400:]:
            sys.exit(f"{path}: already ends with an attribution block")
        open(path, "wb").write(data + blk)
        print(path, sha(data), sha(data + blk), licence(path))


def show(commit, path):
    if commit == ".":                      # the working tree
        return open(path, "rb").read()
    r = subprocess.run(["git", "show", f"{commit}:{path}"], capture_output=True)
    if r.returncode != 0:
        sys.exit(f"git show {commit}:{path}: {r.stderr.decode().strip()}")
    return r.stdout


def verify(base, head, record):
    n = 0
    for line in open(record):
        if line.startswith("#") or not line.strip():
            continue
        path, before, after, lic = line.split()
        old, new = show(base, path), show(head, path)
        if lic != licence(path) or sha(old) != before or sha(new) != after or new != old + block(path):
            sys.exit(f"FAIL {path}: at {head} it is not the file of {base} followed by its attribution block")
        n += 1
    print(f"attribution-blocks: ok: {n} record(s) at {head} equal their text at {base} followed by the block")


def self_test():
    for p in ("docs/replay/x.txt", "review/y.md", "numerics/results-z.txt"):
        b = block(p)
        assert b.startswith(b"\n") and b.endswith(b"\n") and b.count(b"SPDX-FileCopyrightText") == 1
        assert (b"CC-BY-4.0" in b) == p.startswith(("docs/", "review/"))
    assert block("a.md").strip().startswith(b"<!--") and block("a.md").strip().endswith(b"-->")
    assert all(l.startswith(b"# ") for l in block("a.txt").strip().split(b"\n"))
    print("attribution-blocks self-test: PASS")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a == ["--self-test"]:
        self_test()
    elif len(a) == 2 and a[0] == "add":
        add(a[1])
    elif len(a) == 4 and a[0] == "verify":
        verify(a[1], a[2], a[3])
    else:
        sys.exit(__doc__)
