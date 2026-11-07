<!-- Adversarial review of S4.4 and the dependency surface (fresh-context agent, prompt review/prompts/S44-adversarial.md), commit e5da8a5. Verbatim final report. Answers: review/2026-11-07-S44-answers.md. -->

e5da8a5fa9b6b381371332f588f02c8aac697724

# Adversarial review: S4.4 and the dependency surface (commit e5da8a5)

I did not modify the repository, git state, `build/` or `.lake`. All scratch work is under `/tmp/adv6/`. I ran one Lean process at a time under `nice -n 10`.

## Verdict
- **S4.4 statement and proof:** no findings. The closed form is numerically correct for both signs of the discriminant.
- **The claim "a downstream project can check that it depends on exactly the reviewed statements":** false as the README words it. I built a modified OscInt that passes the README's recommended invocation even though `D4LimitStatement := True` (B1).

## 1. Statement and proof (no findings)

**Statement against the docs.**
- `D4ConstantClosedFormStatement` (`OscInt/Statements/D4Limit.lean`) matches `docs/statements.md` S4.4 clause for clause.
- `disc` uses the standard normalisation (x³+y³ has disc −27 < 0, the hyperbolic umbilic).
- The file hash `722952f5…` equals the stamp e2d7771c.
- `Challenge/D4Limit.lean` (`0e661c0a…`) and `comparator-S44.json` (`ab31e81d…`) equal the stamped manifest.

**Numerics (mpmath, 30 digits, `/tmp/adv6/num.py`, `/tmp/adv6/num2.py`).**
- I = Γ(2/3)/2 to 4·10⁻²³ relative (0.6770589697132002…).
- I computed c_C = I·J/3 from the definition, with quadrature breakpoints at the zeros of C(cos θ, sin θ), for five cubics. Three have all coefficients nonzero: (1,2,3,5) disc −367; (1,−2,−3,5) disc 169; (2,1,−7,3) disc 1053. The other two are (1,0,0,1) disc −27 and (−1,3,4,−2) disc 940.
- In every case it equals the closed form to about 10⁻¹¹. The disc < 0 formula has the √3 and the disc > 0 formula does not, and both are confirmed.
- An independent check that does not use the definition: ∬e^{it(x³+y³)} = (Γ(1/3)/√3 · t^{−1/3})², so c = Γ(1/3)²/3. This matches Γ(1/3)²/(√3·27^{1/6}).

**Proof.**
- Assembly `d4ConstantClosedForm_of` (`OscInt/D4/ClosedForm.lean`): I re-derived the algebra by hand and it is correct for both signs.
- `cubicComp` really is the coefficient vector of C∘g. `cubicForm_cubicComp` and `disc_cubicComp` are proved by `ring`, and I checked the (1,1)/(1,−1) extraction by hand.
- No part has an unsatisfiable hypothesis: the Facts are hypothesis-free apart from `disc ≠ 0` / `det2 ≠ 0`.
- No junk value can matter. The final theorem is kernel-checked and its statement does not mention `cubicComp` or `lineMoment`, so a wrong auxiliary definition could not make a false final statement pass. The only fidelity question is the statement itself, and the numerics settle it.
- The part files contain none of `sorry`, `native_decide`, `set_option`, `axiom`, `macro` or `elab`.
- Axioms of `OscInt.d4ConstantClosedForm` (my own run): [Classical.choice, Quot.sound, propext].

## 2. Trust chain for S4.4 (sound)
- The replay record `docs/replay/2026-11-06-S44-verify-all.txt` (1c7ebe3) shows:
  - TYPE-OK for d4ConstantClosedForm;
  - `comparator-S44.json` accepted by six kernels;
  - the S44 challenge export hash equal to the stamp;
  - 11 commitments equal to their stamps.
- HEAD differs from 1c7ebe3 only in documentation.

## 3. Dependency surface

**B1 — BLOCKER. `tools/oscint_check.py` L104–110 and L40, README L60–68.** The file-hash check proves the statement *file* is unchanged, but nothing ties the statement *constant* to that file.
- **Failure scenario, reproduced in `/tmp/adv6/A/`:**
  - The modified package ships `OscInt/Statements/*` byte-identical and an unchanged `stamps/statements.json`, but its `OscInt` does not import them.
  - It defines `OscInt.Statements.D4LimitStatement : Prop := True` and `theorem OscInt.d4Limit : D4LimitStatement := trivial`.
  - I ran the repository's unmodified checker with the real `--expect-sha256`: "ok: 4 statement file(s) match their stamps", "ok: S4.2 OscInt.d4Limit … (axioms [])", **PASS**, rc 0.
- A stale or swapped `.olean` behind unchanged sources gives the same result: the checker hashes sources but checks oleans (lesson 5's failure, downstream).
- Only `--commitments` would catch it, and the README invocation and the policy recommendation leave it off.
- **Fix:**
  - In the Lean step, require `env.getModuleIdxFor? stmt` to be the module of the listed `file`.
  - Make the commitment check the default, or at least the documented CI invocation.
  - Add a negative control for this case.
  - Until then, reword README L61–62 ("no edited file").

**M1 — MAJOR. Kernel-unchecked theorems are invisible to the axiom check (`oscint_check.py` L42).**
- **Failure scenario, reproduced in `/tmp/adv6/B/`:**
  - The modified `OscInt` imports the real `OscInt.Statements.D4Limit` and adds `OscInt.d4Limit` with value `True.intro`, via `addDecl` under `set_option debug.skipKernelTC true`.
  - The checker reports the standard axioms only, then PASS.
  - The statement is genuine, so `--commitments` would pass as well.
- README L62 says "no extra axiom", and L71 only says the checker does not replay proofs in *independent* kernels. In fact no kernel checks imported declarations at all.
- **Fix:** replay the closure of each `proved_by` through the kernel in the checker (lean4checker-style `Environment.replay`, or `leanchecker` on the OscInt modules), or say plainly that the downstream check trusts the oleans.

**M2 — MAJOR. Mathlib and toolchain mismatch are not checked.**
- `mathlib_rev` and `lean_toolchain` are printed (L100) but never compared with the consumer's `lake-manifest.json` or `lean-toolchain`.
- Lake builds OscInt against the root project's Mathlib. A consumer on another Mathlib therefore passes checks 1–3 with every statement closure possibly changed (`Real.rpow`, integral, `fderiv`). The `--commitments` failure message even guesses "a different Mathlib?".
- **Fix:** compare both values by default (cheap), fail on mismatch, and add a negative control.

**M3 — MAJOR. The checker certifies itself, and the expected hash has no independent source.**
- The README runs the checker from `.lake/packages/oscint/tools/` (inside the package being checked), and `--commitments` runs the package's own `oscint-commit-env`. A modified package can ship a checker that always passes.
- `--expect-sha256 <sha256 … at the tag you pinned>` has no published value. CI computes it from the same checkout (`ci.yml` L69), so check 1 is vacuous there and only detects later drift.
- Pinning a git commit hash already gives that much.
- **Fix:**
  - Publish the statements.json SHA-256 in the release notes, timestamped with the stamps.
  - Tell consumers to vendor the checker at a pinned hash.
  - Say in the README that, without these, the check detects accidental drift, not tampering.

**M4 — MAJOR. The re-freeze rule (`docs/policy.md` L41–57) promises a review it cannot deliver.**
- The closure of S4.4 has 4,874 declarations, 158,191 lines and 3.7 MB (`build/commit/…ClosedFormStatement.env.txt`).
- The lines use global numbered ids (`E<i> …`), so any change early in byte order renumbers every later line. A `diff` of old against new is then essentially the whole file, which "one blind referee" cannot read (step 3a).
- With closures of thousands of Mathlib constants (33,099 for S4.3 per lessons 18), step 2's "unchanged → nothing to do" will almost never apply.
- The rule also has no branch for a frozen file that no longer elaborates under the new Mathlib. That forces new constant names, which in turn changes the `proved_by` and stable-surface promises.
- Step 2 is sound in itself: an identical closure means the same meaning.
- **Fix:**
  - Emit per-declaration canonical hashes with local numbering.
  - Add a tool that lists the changed constants and pretty-prints their old and new values.
  - Add the "does not elaborate" case to the rule.

**MINOR.**
- `tools/test_oscint_check.sh`:
  - There is no negative control for the `--commitments` path, for B1, M1 or M2, or a defeq-only type. This violates lessons 18. I confirmed separately (`/tmp/adv6/D/`) that a defeq-only type is correctly rejected.
  - The positive run uses neither `--expect-sha256` nor `--commitments`.
- `tools/src/bin/statements.rs` / checker check 2: only files that contain a statement are hashed. A future closure file holding helper definitions and no statement would go unchecked. Today the closure files D4.lean and StationaryPhase.lean happen to contain statements.
- `stamps/statements.json` says `"version": "0.2.0"` and the checker prints "OscInt 0.2.0 (11 statements…)". But v0.2.0 did not have S4.4 proved, and the checker's error message says statements.json "exists from OscInt v0.3.0".
- `CHANGELOG.md` L10 lists S4.4 under "### Machine-checked". STATUS and README reserve that term until the post-proof reviews exist ("proved and replayed; post-proof review pending").
- `docs/STATUS.md` L74 says "comparator accepted all eight configurations". There are seven `comparator*.json` and the record shows seven accepted.

**NIT.**
- The README "Documents" table omits `docs/proof-S44.md` and `docs/policy.md`.
- The checker's Lean prelude has no `import Lean`; it relies on OscInt importing it transitively. My fake package failed to elaborate until I added it.
- In `docs/policy.md` L18–22 the Minor and Major definitions overlap for 0.x.0. Because `version` is part of statements.json, every patch release breaks the consumer's pin.
- No committed record shows the `consumer` CI job or `test_oscint_check.sh` passing; local ConsumerControls oleans exist.

## 4. Prose
- **README, STATUS, HANDOFF:** their S4.4 status wording is correctly hedged. The CHANGELOG heading and the STATUS "eight" are covered under MINOR.
- **Lessons 19–21:** accurate. The S4.4 names are in `MathlibNames.lean` L26–47 with full signatures, as lesson 19 says.
- **Real overclaim:** README L61–62 and policy L23–25 ("depend on exactly those statements, with no edited file and no extra axiom"; "any change to the statement list fails its CI"). B1, M1, M2 and M3 refute these as written.

## Reproductions
- `/tmp/adv6/A/OscInt.lean`: redefined constant, PASS (B1).
- `/tmp/adv6/B/OscInt.lean`: kernel-skipped theorem, PASS (M1).
- `/tmp/adv6/C/`: the real package, positive run, all 11 OK.
- `/tmp/adv6/D/`: defeq-only control, FAIL as expected.

Each directory has a `bin/lake` stand-in that sets `LEAN_PATH` in place of `lake env`, so no Lake build was run.
