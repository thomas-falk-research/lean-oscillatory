<!-- Adversarial review of milestone M1 by a fresh-context agent (model output, not a human referee).
Prompt: review/prompts/S1-adversarial.md (sha256 4079d1f2b4065a6b4979e3d766eba93af8f06ba0b782eaedc6fbd148bfe1dfad).
Read: commit 402e92a (and faabe5c for the two files noted). Report verbatim below the rule; the lead's answers follow. -->

---

`git rev-parse HEAD` at start: 402e92a5224806d5014cf66c19fc5f1ff87f3f43

HEAD moved to faabe5c61ff2f8f6e8ab84d1c8fa3d92cc0d38f9 while I was reviewing. That commit came from another session and changes `Makefile`, `tools/src/bin/challenge.rs`, `.github/workflows/ci.yml`, `docs/lessons.md` and adds `docs/replay/2026-11-05-M1.txt`. I read `challenge.rs` and the replay record at faabe5c, and everything else at 402e92a. Line numbers below are for those versions.

# Adversarial review, S1 (van der Corput)

**Bottom line.** The three statements are true, not vacuous, and match `docs/statements.md`. The final theorems have exactly the frozen types and use only the three standard axioms. What fails is the claim "machine-checked as stated": no repository evidence shows the comparator or the stamped commitments were checked against the proved state, and the stamped commitments are never compared automatically at all.

## 1. Statements (`OscInt/Statements/VanDerCorput.lean` against `docs/statements.md`)

**Checks that passed:**
- **Faithfulness:** quantifiers, hypotheses, constants (3, 8/√μ, 18·μ^(−1/3)) and the `ampNorm = ‖ψ b‖ + ∫‖ψ'‖` orientation all match the doc.
- **Lean conventions:**
  - `-(1:ℝ)/3` parses as −1/3.
  - Division and `√` appear only under `0 < ν` or `0 < μ`.
  - The integrand is continuous on `[a,b]`, so the zero value Lean gives non-integrable integrals is never reached.
  - `IntervalIntegrable ψ'` stops `∫‖ψ'‖` from collapsing to 0.
- **Degenerate cases:**
  - a = b: `Ioo` is empty and the integral is 0, so the bound holds trivially.
  - Large p: the hypotheses are on φ alone, so p plays no role in them.
  - ψ' unbounded but integrable (ψ = √x): allowed. The bound is still true, because FTC needs only continuity on `Icc`, derivatives on `Ioo` and integrability.
- **Vacuity and bite, my Lean probe** (`/tmp/adv/Bite.lean`, compiles against the built library):
  - `osc_lin`: ∫₀^π e^{ix} dx = 2i.
  - `bite`: instantiates `OscInt.vanDerCorput_one` on φ = x, ν = 1, [0, π], ψ = 1. The hypotheses are discharged directly.
  - `shape_with_constant_one_false`: the same statement with constant 1 is refuted.
  - So the hypothesis set is satisfiable by non-trivial data, and the statement has real content (any constant below 2 would be false).
- **`StatementTypes.lean`** (rerun by me): all three lines print TYPE-OK.
- **Axioms:** `#print axioms vanDerCorput_three` gives [propext, Classical.choice, Quot.sound].

**Findings:**
- **MINOR — `docs/statements.md:41-44`; `VanDerCorput.lean:28-30`.** S1.1 assumes more than Stein:
  - φ′ must be differentiable on (a,b) and continuous on [a,b].
  - This excludes φ′ that is only monotone (e.g. piecewise linear) or that blows up at an endpoint.
  - S1.2 and S1.3 likewise need lower-order derivatives continuous up to the endpoints.
  - This is documented, but "This is weaker than Stein" is ambiguous.
  - Fix: write "the theorem is weaker than Stein's (stronger hypotheses): it excludes …" and list the excluded cases.

## 2. Trust chain

- **MAJOR — no recorded comparator PASS or commitment check for the proved state.**
  - `docs/replay/2026-11-05-M1.txt` (commit 5553b78) has no `comparator` or `commit` step.
  - `build/skipped/` holds no verdicts, and no committed file records `lake comparator` accepting the solution.
  - faabe5c ("comparator SKIPPED until a solution exists") arrived after the proof, and its CI result is not in the repository.
  - `README.md:28-34` lists the comparator as part of the chain, so "machine-checked as stated" is not yet supported by evidence.
  - I did not run `make comparator` or `make commit`, as instructed.
  - I did check by hand:
    - `build/challenge/challenge.ndjson` hashes to 7fe4db8d…, which equals the stamped `challenge-export` line.
    - HEAD's `OscInt/Statements/VanDerCorput.lean`, `Challenge/*`, `comparator.json`, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` hash to their values in `stamps/20261105T203058Z-7516eb518dce/manifest.txt`.
  - Fix: run `make verify-all` on HEAD, commit the full output (including the comparator verdict line), and only then update STATUS.
- **MAJOR — stamped commitments are never compared with recomputed ones.**
  - `tools/src/bin/stamp.rs:147` skips `commitment` and `challenge-export` lines on verify.
  - `stamp.rs:150-160` checks file hashes at the stamped commit, not at HEAD, so `stamp-verify` says nothing about HEAD.
  - `tools/src/bin/commit.rs:57-73` only checks that the two producers agree. It never compares with the manifest.
  - The only automatic link from HEAD to the stamp is the challenge-export hash in `challenge.rs:329-335`. That hash is checked against `LATEST_STAMP` (`Makefile:72`), the lexically newest stamp directory.
  - Failure scenario: edit `VdC1Statement`, run `make stamp`, and `make comparator` passes against the new stamp without complaint. The commitments documented in `docs/commitment-format.md` are recorded but never enforced.
  - Fix:
    - Pin the S1 stamp directory (e.g. in `comparator.json`) instead of using the newest.
    - Make `make commit` (or `stamp-verify`) fail unless `build/commit/commitments.txt` equals the pinned stamp's `commitment` lines.
    - Check that HEAD's `OscInt/Statements/*.lean` hashes equal the stamped ones.
- **MINOR — `README.md:47` and `Challenge/VanDerCorput.lean:1`.** The README calls `Challenge/` "frozen `sorry` copies", but the challenge imports the live `OscInt.Statements.VanDerCorput`.
  - The comparator's challenge-versus-solution comparison is therefore trivially satisfied: both sides share one module.
  - Only the stamped export hash catches a statement edit, and that hash is weakened by the previous finding.
  - Fix: make `Challenge/` a verbatim copy of the statement definitions in their own module, or correct the README and state that the hash is the only protection.
- **MINOR — `StatementTypes.lean:6-7`.** The comment says `guard.rs` checks that every theorem STATUS names as proved appears in `StatementTypes`. No such check exists: `grep STATUS tools/src/bin/*.rs` finds nothing.
  - Also, nothing checks that the `#assert_type_is` pairs match `comparator.json` `theorem_names`. They agree today by hand.
  - Fix: implement both checks in `guard.rs`, or delete the claim.
- **MINOR — `tools/src/bin/guard.rs:99-103`.** The forbidden list lacks `run_meta`, `run_elab` and `import Lean`/`Lean.Elab` imports. These can change the environment from inside a library file.
  - The kernel replay is the real check, and it passed, so this is a tripwire gap only.
  - Fix: add those tokens.
- **NIT — `Axioms.lean:48`.** `isInternalDetail` drops `private` theorems (their names have `_private` and numeric parts). That would show up as a count mismatch, so it fails loudly.
  - It does not matter for S1: the final theorems are enumerated, clean, and their whole closure is re-checked from the export by `replay.rs:check_export`.
- **NIT — `tools/src/bin/replay.rs:25-42`.** `leanchecker` is run per module only on `OscInt` modules, not `Blueprint`. The from-export kernels do cover the closure.
- **NIT — `tools/src/bin/challenge.rs:339`.** The comparator counts as accepted on exit 0 with no "panic". Unlike `replay.rs:verdict`, it requires no acceptance line.
- **NIT — commitment scope (`docs/commitment-format.md:24-28`).** It omits binder names and annotations, theorem proofs and recursor rules. None of these changes the meaning of the statement Props; harmless here.

## 3. Numerics (read, not run)

`numerics/results-2026-11-05.txt` and `numerics/src/main.rs`:
- The amplitude-norm arithmetic is correct: 9/ν for ψ = 1+x², and cos1 + 2(1−cos1) for ψ = cos x.
- **MINOR.** The probes test only smooth polynomial phases and smooth, non-sign-changing ψ′.
  - Worst ratio is 0.53, with no near-extremal case. The linear phase over half a period would give 2/3 for k=1.
  - Nothing tests the generality the Lean statements actually claim: φ not C², merely differentiable φ″/φ‴, ψ′ unbounded but integrable.
  - They agree with the statements but do not stress the hypotheses as stated in Lean. Acceptable, since numerics are labelled "never evidence".

## 4. Prose

- **MINOR (understated / stale):** these still say "not started" or "—" although the proof and the replay exist:
  - `README.md:12` and `README.md:17`
  - `docs/STATUS.md:8` (Proof and Replay columns)
  - `docs/progress.md` (no M1 entry)
  - Fix: update them once the comparator evidence above exists.
  - When updating, say that the proof route is a port of Roos–Praveen (`roos-j/lean-oscillatory`, PR #39406), as `Final.lean:11` does. Do not present it as independent; `docs/prior_art.md` marks S1 ANTICIPATED.
- **NIT — `docs/HANDOFF.md:34`:** refers to `OscInt/Statements/S1.lean`; the file is `VanDerCorput.lean`.
- **No overclaim found:** `docs/prior_art.md` is appropriately hedged.

## Summary

| Severity | Count | Findings |
|---|---|---|
| BLOCKER | 0 | — |
| MAJOR | 2 | no recorded comparator/commitment verdict for the proved state; stamped commitments never enforced and the stamp is chosen as the newest |
| MINOR | 7 | |
| NIT | 5 | |

---

## Lead's answers (2026-11-05)

- MAJOR (no recorded verdict): fixed. `make verify-all` was run on the committed tree after the fixes below and its
  full output is committed as `docs/replay/2026-11-05-M1-verify-all.txt` (comparator acceptance line included).
- MAJOR (commitments not enforced; newest stamp used): fixed. `stamps/pins.txt` pins each statement and the challenge
  to a stamp directory; `make commit` now fails unless every recomputed commitment equals the pinned stamp's
  `commitment` line and every file under `OscInt/Statements/` has the hash that stamp recorded
  (`tools/src/bin/commit.rs`, `enforce_pins`); `make comparator` uses the pinned challenge stamp, not the newest.
  Negative control run: a pin pointing at a copy of the manifest with one altered commitment fails with
  "commitment … differs from the one stamped in …".
- MINOR (Challenge imports the live statement module): accepted; the README now says the stamped challenge-export
  hash (now enforced against the pinned stamp) and the pinned statement-file hashes are the protection, and the
  comparator adds the kernel checks and the axiom list. A verbatim copy would duplicate definitions without adding a
  check the hashes do not already make.
- MINOR (StatementTypes comment): fixed. The guard now checks every `comparator.json` theorem has an
  `#assert_type_is` line; the STATUS claim is removed from the comment.
- MINOR (guard tokens): fixed: `run_meta`, `run_elab`, and `import Lean…` in library files are forbidden (tests added).
- NIT (comparator acceptance line): fixed: "Your solution is okay!" is required.
- MINOR (S1.1 wording in `docs/statements.md`): fixed in the docs' modelling-choice list (the stamped Lean header is
  unchanged; see the pre-proof review answers).
- MINOR (numerics do not stress the general hypotheses): accepted; numerics are tooling, not evidence. Recorded in
  HANDOFF as a possible improvement (piecewise-linear φ′, unbounded integrable ψ′).
- MINOR/NIT (stale prose, HANDOFF path): fixed in README, STATUS, progress and HANDOFF, crediting the Roos–Praveen
  route.
- NITs (private theorems drop out of the audit enumeration but fail loudly by count; Blueprint not replayed per
  module but covered by the export; commitment scope): accepted as stated.
