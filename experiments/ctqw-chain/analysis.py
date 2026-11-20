#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0
"""The registered analysis (docs/prereg/2026-11-16-CTQW-chain.md, section 5). Standard library only. Fixed before
any hardware data exists; a change after the first run is a deviation and must be recorded as one.

Input: a JSON file {"runs": [{"sites": M, "time": "1", "repetition": r, "shots": n,
                              "counts": {"000010000": 123, ...}, "meta": {...}}, ...]}
       Bit strings are written site 0 first (left-most character = site 0). The run file says so in "bit_order":
       "site0-left"; any other value is refused.
       and the certified reference (reference.json).
For each run: keep the shots with exactly one excitation; the kept fraction; the post-selected site distribution; its
total-variation distance to the certified Trotter reference; the second moment about the centre.
Decision per (sites, time): CONSISTENT if the distance is at most the registered tolerance in at least 4 of 5
repetitions; otherwise NOT CONSISTENT; INVALID if a run keeps fewer than the registered minimum of shots.
"""
import json
import sys
from fractions import Fraction as F

MIN_KEPT = 500
REPS_REQUIRED = 4


def mid(e):
    return (F(e["lo"]) + F(e["hi"])) / 2


def analyse(runs, reference, tolerance):
    out = []
    groups = {}
    for run in runs["runs"]:
        M, ts = int(run["sites"]), str(run["time"])
        ref = reference["chains"][str(M)]["times"][ts]
        c = reference["chains"][str(M)]["start"]
        counts = [0] * M
        total = 0
        for bits, n in run["counts"].items():
            if len(bits) != M or set(bits) - {"0", "1"} or not isinstance(n, int) or n < 0:
                raise ValueError(f"bad count entry {bits!r}: {n!r}")
            total += n
            if bits.count("1") == 1:
                counts[bits.index("1")] += n
        kept = sum(counts)
        if total != int(run["shots"]):
            raise ValueError("counts do not add up to shots")
        row = {"sites": M, "time": ts, "repetition": run["repetition"], "shots": total, "kept": kept,
               "kept_fraction": kept / total if total else None}
        if kept < MIN_KEPT:
            row["status"] = "INVALID"
        else:
            p = [F(n, kept) for n in counts]
            q = [mid(e) for e in ref["trotter"]]
            tvd = sum(abs(a - b) for a, b in zip(p, q)) / 2
            row.update({"status": "OK", "populations": [float(x) for x in p], "tvd": float(tvd),
                        "moment": float(sum((a - c) ** 2 * p[a] for a in range(M))),
                        "moment_reference": float(mid(ref["moment_trotter"])),
                        "within_tolerance": bool(tvd <= F(str(tolerance[str(M)][ts])))})
        out.append(row)
        groups.setdefault((M, ts), []).append(row)
    decisions = []
    for (M, ts), rows in sorted(groups.items()):
        if any(r["status"] == "INVALID" for r in rows) or len(rows) != 5:
            d = "INVALID"
        else:
            d = "CONSISTENT" if sum(r["within_tolerance"] for r in rows) >= REPS_REQUIRED else "NOT CONSISTENT"
        decisions.append({"sites": M, "time": ts, "decision": d, "tvd": [r.get("tvd") for r in rows],
                          "tolerance": tolerance[str(M)][ts]})
    return {"format": "oscint-ctqw-analysis/1", "runs": out, "decisions": decisions}


if __name__ == "__main__":
    runs = json.load(open(sys.argv[1]))
    if runs.get("bit_order") != "site0-left":
        sys.exit("analysis: bit_order must be 'site0-left'")
    reference = json.load(open(sys.argv[2]))
    tolerance = json.load(open(sys.argv[3]))["tolerance"]
    print(json.dumps(analyse(runs, reference, tolerance), indent=1))
