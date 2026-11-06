#!/usr/bin/env python3
"""Check, from a downstream Lake project, that the OscInt you depend on is exactly the reviewed one.

Run it from your project's root after `lake build` (Python 3.8+, standard library only):

    python3 .lake/packages/oscint/tools/oscint_check.py --statement OscInt.Statements.D4LimitStatement

Checks, in order (each failure names the file or theorem and the likely fix):
  1. `stamps/statements.json` of the OscInt package parses, and (with --expect-sha256) has the hash you pinned.
  2. Every statement file listed there has the SHA-256 its stamp records (no frozen file edited).
  3. Lean: each selected statement that has a proof is proved by its listed theorem, whose type is *syntactically*
     the statement constant, and whose axioms are only propext, Classical.choice, Quot.sound
     (runs `lake env lean` on a generated file in a temporary directory).
  4. With --commitments: recomputes each statement's commitment (SHA-256 of its definitional closure,
     docs/commitment-format.md) with the package's `oscint-commit-env` and compares it with the stamped one.

What it does not do: replay proofs in independent kernels or re-review statements. Those are OscInt's own trust
chain (README, "What a reader must trust"); this script checks that you are using its output unchanged.
Exit status: 0 all checks passed, 1 a check failed, 2 usage or environment error.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
FORMAT = "oscint-statements 1"

LEAN_PRELUDE = """open Lean Elab Command

elab "#oscint_check " thm:ident stmt:ident : command => do
  let env ← getEnv
  let some ci := env.find? thm.getId | IO.println s!"OSCINT-FAIL {thm.getId} : unknown constant"
  unless ci matches .thmInfo _ do IO.println s!"OSCINT-FAIL {thm.getId} : not a theorem"; return
  unless ci.type == mkConst stmt.getId [] do
    IO.println s!"OSCINT-FAIL {thm.getId} : its type is not the constant {stmt.getId}"; return
  let axs ← liftCoreM <| Lean.collectAxioms thm.getId
  IO.println s!"OSCINT-OK {thm.getId} : {stmt.getId} axioms {axs.toList}"
"""


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def fail(msg):
    print(f"oscint-check: FAIL: {msg}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--project", default=".", help="your Lake project root (default: .)")
    ap.add_argument("--oscint", help="the OscInt package directory (default: PROJECT/.lake/packages/oscint)")
    ap.add_argument("--statement", action="append", default=[],
                    help="a statement your project relies on (repeatable; default: every proved statement); "
                         "it must be listed and proved")
    ap.add_argument("--expect-sha256", help="the SHA-256 of stamps/statements.json you pinned")
    ap.add_argument("--commitments", action="store_true",
                    help="also recompute the statement commitments (runs `lake exe oscint-commit-env`)")
    ap.add_argument("--import", dest="imports", action="append", default=[], metavar="MODULE",
                    help="also import MODULE in the Lean check (repeatable; e.g. a module of your own)")
    ap.add_argument("--no-lean", action="store_true", help="skip the Lean checks (3 and 4)")
    a = ap.parse_args(argv)

    project = os.path.abspath(a.project)
    oscint = os.path.abspath(a.oscint or os.path.join(project, ".lake", "packages", "oscint"))
    sj = os.path.join(oscint, "stamps", "statements.json")
    if not os.path.isfile(sj):
        print(f"oscint-check: ERROR: {sj} not found. Pass --oscint DIR, or run `lake update oscint` so the "
              "package is checked out (it exists from OscInt v0.3.0).")
        return 2
    try:
        with open(sj, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError) as e:
        fail(f"{sj} does not parse: {e}")
        return 1
    if data.get("format") != FORMAT:
        fail(f"{sj}: format {data.get('format')!r}, this checker reads {FORMAT!r}; use the checker shipped "
             "with that OscInt version")
        return 1
    bad = 0
    if a.expect_sha256:
        got = sha256(sj)
        if got != a.expect_sha256.lower():
            fail(f"stamps/statements.json has sha256 {got}, you pinned {a.expect_sha256}: the statement list "
                 "changed. Read CHANGELOG.md for the new version before updating your pin.")
            bad += 1
    stmts = {s["name"]: s for s in data["statements"]}
    print(f"oscint-check: OscInt {data['version']} ({len(stmts)} statements, Lean {data['lean_toolchain']}, "
          f"Mathlib {data['mathlib_rev'][:12]})")

    for s in stmts.values():
        p = os.path.join(oscint, s["file"])
        if not os.path.isfile(p):
            fail(f"{s['file']} is missing from {oscint}")
            bad += 1
        elif sha256(p) != s["file_sha256"]:
            fail(f"{s['file']} has sha256 {sha256(p)}, its stamp {s['stamp']} records {s['file_sha256']}: "
                 "the frozen statement file was edited. Re-fetch the package (`lake update oscint`).")
            bad += 1
    if not bad:
        print(f"oscint-check: ok: {len({s['file'] for s in stmts.values()})} statement file(s) match their stamps")

    for n in a.statement:
        if n not in stmts:
            fail(f"{n} is not a pinned OscInt statement; known: {', '.join(sorted(stmts))}")
            bad += 1
        elif stmts[n]["proved_by"] is None:
            fail(f"{n} ({stmts[n]['label']}) is stated but not proved in OscInt {data['version']}")
            bad += 1
    selected = [stmts[n] for n in a.statement if n in stmts and stmts[n]["proved_by"]] or \
        [s for s in stmts.values() if s["proved_by"]]
    if a.no_lean:
        return 1 if bad else 0

    with tempfile.TemporaryDirectory() as tmp:
        lf = os.path.join(tmp, "OscIntCheck.lean")
        with open(lf, "w", encoding="utf-8") as f:
            f.write("".join(f"import {m}\n" for m in ["OscInt"] + a.imports))
            f.write(LEAN_PRELUDE)
            for s in selected:
                f.write(f"#oscint_check {s['proved_by']} {s['name']}\n")
        r = subprocess.run(["lake", "env", "lean", lf], cwd=project, capture_output=True, text=True)
        out = r.stdout + r.stderr
        if r.returncode != 0 and "OSCINT-" not in out:
            print(f"oscint-check: ERROR: `lake env lean` failed in {project} (did you run `lake build`?):\n{out}")
            return 2
        for s in selected:
            m = re.search(rf"^OSCINT-OK {re.escape(s['proved_by'])} : {re.escape(s['name'])} axioms \[(.*)\]$",
                          out, re.M)
            if not m:
                why = re.search(rf"^OSCINT-FAIL {re.escape(s['proved_by'])} : (.*)$", out, re.M)
                fail(f"{s['proved_by']}: {why.group(1) if why else 'no result line'} ({s['label']})")
                bad += 1
                continue
            axs = {x.strip() for x in m.group(1).split(",") if x.strip()}
            if not axs <= PERMITTED:
                fail(f"{s['proved_by']} uses axioms {sorted(axs - PERMITTED)} beyond {sorted(PERMITTED)}")
                bad += 1
            else:
                print(f"oscint-check: ok: {s['label']} {s['proved_by']} : {s['name']} (axioms {sorted(axs)})")

        if a.commitments:
            out_dir = os.path.join(tmp, "commit")
            r = subprocess.run(["lake", "exe", "oscint-commit-env", out_dir], cwd=project, capture_output=True,
                               text=True)
            if r.returncode != 0:
                print(f"oscint-check: ERROR: `lake exe oscint-commit-env` failed:\n{r.stdout}{r.stderr}")
                return 2
            for s in selected:
                p = os.path.join(out_dir, s["name"] + ".env.txt")
                got = sha256(p) if os.path.isfile(p) else None
                if got != s["commitment"]:
                    fail(f"{s['name']}: recomputed commitment {got}, stamped {s['commitment']} "
                         f"({s['stamp']}): the definitions the statement depends on differ (a different Mathlib?)")
                    bad += 1
                else:
                    print(f"oscint-check: ok: commitment of {s['name']} equals its stamp")

    print("oscint-check: " + ("FAIL" if bad else "PASS") + f" ({bad} problem(s))")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
