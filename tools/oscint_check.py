#!/usr/bin/env python3
"""Check, from a downstream Lake project, that the OscInt you depend on is exactly the reviewed one.

Run it from your project's root after `lake build` (Python 3.8+, standard library only):

    python3 .lake/packages/oscint/tools/oscint_check.py --statement OscInt.Statements.D4LimitStatement

Checks, in order (each failure names the file or theorem and the likely fix):
  1. `stamps/statements.json` of the OscInt package parses, and (with --expect-sha256) has the hash you pinned.
  2. Your project uses the Lean toolchain and the Mathlib revision OscInt was checked with (`lean-toolchain`,
     `lake-manifest.json`); a different Mathlib can change what a statement means.
  3. Every file under `OscInt/Statements/` has a SHA-256 recorded by a pinned stamp (no frozen file edited).
  4. Lean: each selected statement constant is declared in the module of its frozen file; its proving theorem's
     type is *syntactically* the statement constant; its axioms are only propext, Classical.choice, Quot.sound.
  5. Kernel replay: `leanchecker` re-checks every OscInt and Blueprint module and every module in the dependency closure of each
     checked theorem (the package's root module `OscInt` may only import) from its .olean, so a
     declaration added with kernel checking switched off, or a stale or swapped .olean, is rejected.
  6. Commitments: recomputes each selected statement's commitment (SHA-256 of its definitional closure,
     docs/commitment-format.md) with `oscint-commit-env` and compares it with the stamped one, so a statement
     constant whose meaning differs from the reviewed one is rejected even if every file hash matches.
  --no-kernel / --no-commitments skip 5 / 6 (--fast skips both); the verdict is then PARTIAL, never PASS: a smoke
  test, not a check that you depend on the reviewed statements.

Trust: this script and `oscint-commit-env` come from the package being checked. Run from the package, it detects
accidental drift (a different version, an edited file, a stale build), not deliberate tampering; for that, keep
your own copy of this script at a reviewed version (its SHA-256 is in the release notes) and pin the SHA-256 of
`stamps/statements.json` from the release notes. Not done here: independent kernels (lean4lean, nanoda, …) and the
review of the statements, which are OscInt's own trust chain (README, "What stays trusted"). Mathlib's .olean files
come from Mathlib's cache and are trusted, as in OscInt's own CI.

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

elab "#oscint_check " thm:ident stmt:ident mod:ident : command => do
  let env ← getEnv
  match env.getModuleIdxFor? stmt.getId with
  | none => IO.println s!"OSCINT-FAIL {thm.getId} : statement {stmt.getId} is not declared in an imported module"; return
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    unless m == mod.getId do
      IO.println s!"OSCINT-FAIL {thm.getId} : statement {stmt.getId} is declared in module {m}, not in {mod.getId}"
      return
  let some ci := env.find? thm.getId | IO.println s!"OSCINT-FAIL {thm.getId} : unknown constant"
  unless ci matches .thmInfo _ do IO.println s!"OSCINT-FAIL {thm.getId} : not a theorem"; return
  unless ci.type == mkConst stmt.getId [] do
    IO.println s!"OSCINT-FAIL {thm.getId} : its type is not the constant {stmt.getId}"; return
  let axs ← liftCoreM <| Lean.collectAxioms thm.getId
  IO.println s!"OSCINT-OK {thm.getId} : {stmt.getId} axioms {axs.toList}"
  -- the modules of every constant the theorem depends on (types and values, transitively), outside the toolchain
  -- and Mathlib's packages: the kernel replay must cover each of them
  let trusted : List Name := [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets,
    `Plausible, `ImportGraph, `LeanSearchClient, `Cli]
  let mut seen : NameHashSet := {}
  let mut stack : Array Name := #[thm.getId]
  let mut mods : NameHashSet := {}
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some i := env.getModuleIdxFor? c then
      let m := env.header.moduleNames[i.toNat]!
      unless trusted.contains m.getRoot do mods := mods.insert m
    if let some d := env.find? c then
      for u in d.type.getUsedConstants ++ ((d.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] do
        unless seen.contains u do stack := stack.push u
  IO.println s!"OSCINT-MODULES {thm.getId} {(mods.toList.map toString).toArray.qsort (· < ·) |>.toList}"
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
    ap.add_argument("--no-kernel", action="store_true", help="skip the kernel replay (verdict PARTIAL)")
    ap.add_argument("--no-commitments", action="store_true", help="skip the commitments (verdict PARTIAL)")
    ap.add_argument("--fast", action="store_true", help="--no-kernel --no-commitments (verdict PARTIAL)")
    ap.add_argument("--commitments", action="store_true", help=argparse.SUPPRESS)  # default since 2026-11-07
    ap.add_argument("--import", dest="imports", action="append", default=[], metavar="MODULE",
                    help="also import MODULE in the Lean check (repeatable; e.g. a module of your own)")
    ap.add_argument("--no-lean", action="store_true", help="skip every Lean check (4, 5, 6); files only")
    a = ap.parse_args(argv)
    if a.fast:
        a.no_kernel = a.no_commitments = True
    skipped = []

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
    print(f"oscint-check: OscInt statements ({len(stmts)} statements, Lean {data['lean_toolchain']}, "
          f"Mathlib {data['mathlib_rev'][:12]})")

    tc_path = os.path.join(project, "lean-toolchain")
    tc = open(tc_path).read().strip() if os.path.isfile(tc_path) else None
    if tc != data["lean_toolchain"]:
        fail(f"your lean-toolchain is {tc!r}, OscInt was checked with {data['lean_toolchain']!r}; use the same "
             "toolchain (copy OscInt's lean-toolchain)")
        bad += 1
    mf_path = os.path.join(project, "lake-manifest.json")
    rev = None
    if os.path.isfile(mf_path):
        try:
            mf = json.load(open(mf_path, encoding="utf-8"))
            rev = next((p.get("rev") for p in mf.get("packages", []) if p.get("name") == "mathlib"), None)
        except ValueError:
            rev = None
    if rev != data["mathlib_rev"]:
        fail(f"your Mathlib revision is {rev!r} (lake-manifest.json), OscInt was checked with "
             f"{data['mathlib_rev']!r}; a different Mathlib can change what the statements mean. Pin Mathlib to "
             "OscInt's revision (or let OscInt's manifest provide it: remove your own mathlib requirement)")
        bad += 1
    files = data.get("statement_files", [])
    for f in files:
        p = os.path.join(oscint, f["file"])
        if not os.path.isfile(p):
            fail(f"{f['file']} is missing from {oscint}")
            bad += 1
        elif sha256(p) != f["sha256"]:
            fail(f"{f['file']} has sha256 {sha256(p)}, its stamp {f['stamp']} records {f['sha256']}: "
                 "the frozen statement file was edited. Re-fetch the package (`lake update oscint`).")
            bad += 1
    on_disk = sorted(os.path.relpath(os.path.join(r, n), oscint).replace(os.sep, "/")
                     for r, _, ns in os.walk(os.path.join(oscint, "OscInt", "Statements")) for n in ns
                     if n.endswith(".lean"))
    extra = sorted(set(on_disk) - {f["file"] for f in files})
    if extra:
        fail(f"statement file(s) {extra} are not in stamps/statements.json (not frozen by any stamp)")
        bad += 1
    if not bad:
        print(f"oscint-check: ok: toolchain and Mathlib match; {len(files)} statement file(s) match their stamps")

    for n in a.statement:
        if n not in stmts:
            fail(f"{n} is not a pinned OscInt statement; known: {', '.join(sorted(stmts))}")
            bad += 1
        elif stmts[n]["proved_by"] is None:
            fail(f"{n} ({stmts[n]['label']}) is stated but not proved in this OscInt")
            bad += 1
    selected = [stmts[n] for n in a.statement if n in stmts and stmts[n]["proved_by"]] or \
        [s for s in stmts.values() if s["proved_by"]]
    if a.no_lean:
        skipped.append("Lean checks")
        print("oscint-check: SKIPPED: Lean checks (--no-lean)")
        print("oscint-check: " + ("FAIL" if bad else "PARTIAL") + f" ({bad} problem(s); skipped: Lean checks)")
        return 1 if bad else 0

    with tempfile.TemporaryDirectory() as tmp:
        lf = os.path.join(tmp, "OscIntCheck.lean")
        with open(lf, "w", encoding="utf-8") as f:
            f.write("".join(f"import {m}\n" for m in ["Lean", "OscInt"] + a.imports))
            f.write(LEAN_PRELUDE)
            for s in selected:
                mod = s["file"][:-len(".lean")].replace("/", ".")
                f.write(f"#oscint_check {s['proved_by']} {s['name']} {mod}\n")
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

        if a.no_kernel:
            skipped.append("kernel replay")
            print("oscint-check: SKIPPED: kernel replay (--no-kernel)")
        else:
            mods = set(os.path.relpath(os.path.join(r, n), oscint)[:-len(".lean")].replace(os.sep, ".")
                       for lib in ("OscInt", "Blueprint")
                       for r, _, ns in os.walk(os.path.join(oscint, lib)) for n in ns if n.endswith(".lean"))
            kbad = []
            # every module in the dependency closure of a checked theorem is replayed; the root module `OscInt` may
            # only import (it is never replayed whole: lessons 14), so a closure constant declared there fails
            for s in selected:
                m = re.search(rf"^OSCINT-MODULES {re.escape(s['proved_by'])} \[(.*)\]$", out, re.M)
                used = {x.strip() for x in m.group(1).split(",") if x.strip()} if m else None
                if used is None:
                    kbad.append((s["proved_by"], "no module list from the Lean check"))
                    continue
                for u in sorted(used):
                    if u == "OscInt":
                        kbad.append(("OscInt", f"declares {s['proved_by']} or a constant it depends on; OscInt's "
                                     "root module may only import"))
                    mods.add(u)
            mods.discard("OscInt")
            mods = sorted(mods)
            for m in mods:
                r = subprocess.run(["lake", "env", "leanchecker", m], cwd=project, capture_output=True, text=True)
                out = (r.stdout + r.stderr).strip()
                if r.returncode != 0 or re.search(r"error|PANIC|problem", out, re.I):
                    kbad.append((m, out.splitlines()[-1] if out else f"exit {r.returncode}"))
            for m, why in kbad:
                fail(f"kernel replay rejected module {m}: {why}")
            bad += len(kbad)
            if not kbad:
                print(f"oscint-check: ok: kernel replay (leanchecker) accepted {len(mods)} module(s)")
        if a.no_commitments:
            skipped.append("commitments")
            print("oscint-check: SKIPPED: commitments (--no-commitments)")
        else:
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
                         f"({s['stamp']}): the definitions the statement depends on differ from the reviewed ones")
                    bad += 1
                else:
                    print(f"oscint-check: ok: commitment of {s['name']} equals its stamp")

    verdict = "FAIL" if bad else ("PARTIAL" if skipped else "PASS")
    print(f"oscint-check: {verdict} ({bad} problem(s)" + (f"; skipped: {', '.join(skipped)})" if skipped else ")"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
