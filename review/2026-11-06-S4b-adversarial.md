<!-- Adversarial review of S4.1', S4.2, S4.3 (fresh-context agent, prompt review/prompts/S4b-adversarial.md), commit f35f35e. Verbatim final report. -->

`f35f35eb730845950473e227c539eb879f6c9978`

# Adversarial review: S4.1′, S4.2, S4.3 (commit f35f35e)

**Verdict:** I found no BLOCKER or MAJOR. Both claims survive:
- "S4.1′, S4.2 and S4.3 are machine-checked as stated."
- "The S4.3 proof is Gamma/Beta/Mellin-free." The check is by constant names, but it is honest and transitive, and I re-ran it independently.

The findings are stale prose (understatements, no overclaims), a qualifier the pre-registration wording needs, and small robustness nits.

Scratch files: `/tmp/adv5/Bite.lean` and `/tmp/adv5/GF.lean`. I ran them with `nice -n 10 lake env lean`, one process at a time. The oleans are current: no source is newer than `.lake/build/lib/lean/OscInt.olean`, and a71b318..f35f35e touches only docs and prompts. I wrote nothing in the repository.

## What I checked and what held

**1. Statements**
- **Freeze.** `OscInt/Statements/D4Limit.lean`, `OscInt/Statements/D4.lean`, `OscInt/Basic.lean`, `Challenge/D4Limit.lean` and `comparator-S41w/S42/S43/S44.json` all have the same sha256 as `stamps/20261106T081634Z-e2d7771c358e/manifest.txt`. The pins in `stamps/pins.txt` name that stamp.
- **Bite.** I proved `adv_bite` with the `x³ + y³` phase and the amplitude from `ampBound_exists_delta`, which has A(0) = 1. Using `OscInt.d4Limit` and `OscInt.d4ConstantPos`, it shows: there exist δ > 0, A, M and c > 0 such that t^{2/3}·‖∫ e^{itφ}A‖ → c. Axioms: propext, Classical.choice, Quot.sound. So S4.2 together with S4.3 gives a nonzero limit, and the result is not vacuous.
- **Elliptic case.** `adv_bite_elliptic` gives the same positive limit for x³ − 3xy² (disc = 108). `adv_s41w_elliptic` applies `OscInt.d4BoundNe` to the elliptic umbilic. So S4.1′ really contains D4⁻.
- **Junk values.**
  - The `limUnder` in `cosMoment` is not junk: S4.3 conjunct 1 proves convergence to it.
  - `angularMoment` is not junk for disc ≠ 0: S4.3 proves the integrand integrable.
  - At disc = 0, `d4Constant` = 0 is junk, but every statement assumes disc ≠ 0. The 2026-11-06 clarification in `docs/statements.md` discloses this.
  - The formula c_C = I·J/3 checks by hand: substituting u = r³|C| gives r dr = (1/3)|C|^{-2/3}u^{-1/3} du, and the sine part cancels because C(θ+π) = −C(θ).
- **Gamma-free check, attacked.** I re-implemented the `GammaFree.lean` closure in `/tmp/adv5/GF.lean`. Every attempt to hide `Real.Gamma` behind a clean type was rejected (33 or 6 forbidden constants each):

  | Hiding attempt | Rejected |
  |---|---|
  | unused `have` | yes |
  | `have` with an aux lambda | yes |
  | instance (`Inhabited ℝ := ⟨Γ 2⟩`) | yes |
  | `match` aux definition | yes |
  | `Classical.choose` witness | yes |
  | `opaque` with a Gamma value | yes |
  | structure default field (`_default`) | yes |

  - My `atk_decide` test was not proof-only (its type mentions Gamma). The proof-only `have` case covers that path.
  - The real closures: `OscInt.d4ConstantPos` has 43 612 constants, 0 forbidden, matching the claim. `D4ConstantPosStatement` has 33 099, 0 forbidden.
  - Every constant in the closure resolves (0 unknown). No constructor of the 908 inductives in it reaches Gamma.
  - I also scanned the S4.3 closure for nearby names: Fourier, Gauss, zeta, Fresnel, Wallis, sinc, Dirichlet, Laplace and mellin give 0 hits. "Stirling" hits only `Nat.stirlingSecond` (combinatorics).
- **Extra.** `OscInt.d4Limit` (53 781 constants) and `OscInt.d4BoundNe` (51 302) are also Gamma-free. The docs do not claim this.

**2. Proof route**
- The final theorems are one-line applications of assemblies whose inputs are Blueprint Props, all proved.
- The guard forbids `opaque`, `axiom`, `elab`, `debug.skipKernelTC`, `addDecl` and similar in `OscInt/`. The axiom audit is clean (458 of 458).
- **S4.3 as frozen:** yes. `d4Limit_of (… ) (hPos : D4ConstantPosStatement)` receives `OscInt.d4ConstantPos` itself (`OscInt/D4/LimitFinal.lean:23`, `OscInt/D4/LimitAssembly.lean:185-188`).
- **S4.1′ as frozen:** no. The theorem `d4BoundNe` is not used. S4.2 reuses the parts (`rescaleFamily`, `cubicGauge`, `gaugeFold`, `gaugeOpen`, `cutoff`) through `exists_piece_bound`. This is what `docs/proof-S42.md` says ("S4.1′ parts D1–D9 … reused"), so nothing is wrong, but "uses S4.1′" would be inaccurate wording.

**3. Trust chain**
- `StatementTypes.lean` has TYPE-OK lines for `d4BoundNe`, `d4ConstantPos` and `d4Limit`.
- The replay record `docs/replay/2026-11-06-S4b-verify-all.txt` (a71b318) shows:
  - comparator-S41w, -S42 and -S43 accepted against the pinned stamp, with export hashes equal to the manifest, in six kernels;
  - leanchecker per module;
  - the result INCOMPLETE only because S4.4 has no proof yet.
- CI run 42200801140 on a71b318 is green, including nanoda built from source ("Checked 54998 declarations with no typechecker errors").

## Findings

**MINOR 1: README and STATUS still say S4.2 and S4.3 are unproved (understatement).**
- `README.md:5` says "the limit and its constant S4.2–S4.4 are stated, not yet proved".
- `README.md:17` says "proofs not started".
- `docs/STATUS.md:54-56` says "none is proved yet".
- The STATUS table rows 13-15 say they are proved and replayed.
- *Failure:* a reader of the README or the STATUS narrative gets the wrong state.
- *Fix:* update README rows 16-17 and line 5, and the STATUS S4.1′–S4.4 paragraph, to "proved and replayed; post-proof review running". Add the record and CI run 42200801140, as the earlier milestones do.

**MINOR 2: `docs/HANDOFF.md` is stale.**
- Lines 6-10 list "Machine-checked" only up to S4.1, and the latest record cited is a0b1fde.
- Lines 23-27, "Next", still plan S4.3 by the π/2 grouping with certified bounds (6% margin). The route-referee clarification replaced that with integration by parts and sin·u^{-4/3} humps. It also still plans S4.2 as future work.
- *Failure:* a new session would redo S4.2 and S4.3, or follow the superseded route.
- *Fix:* rewrite "What exists" and "Next". Next is S4.4 plus the S4.1′/S4.2/S4.3 post-proof reviews.

**MINOR 3: "pre-registered" needs a qualifier; the working Gamma check was not pre-registered.**
- Commit 94f7657 (08:29) pre-registered `GammaFree.lean`, but that version never followed proofs (lesson 18).
- The working version (`value? (allowOpaque := true)` plus `gammaProofControl`) arrived in e89b610, the same commit as the S4.3 proof.
- Neither version is in a TSA stamp: `GammaFree.lean` is absent from the e2d7771 manifest. Only git and GitHub CI times date it.
- *Failure:* a hostile reader sees "the test was changed in the commit that made it pass". The fix only makes the check stronger, and my independent re-run agrees (0 forbidden, 43 612), so the claim stands. Only the wording is the problem.
- *Fix:* in STATUS row 15 and `docs/proof-S43.md:5`, say "pre-registered 94f7657 (did not follow proofs); corrected check introduced with the proof in e89b610; independently re-run by the adversarial referee". Optionally put `GammaFree.lean` into the next stamp.

**MINOR 4: "Gamma-free" means "no forbidden name", and the docs should say so.**
- `GammaFree.lean:24-27` matches name components containing Gamma, Beta, betaIntegral, mellin or Mellin.
- *Failure:* a Mellin/Gamma-type identity proved inline under neutral names would pass. I found no sign of this in the closure (scan above), and the route is integration by parts plus an alternating series.
- *Fix:* in STATUS, the decision record and the README, state the criterion as "no constant whose name contains …, in the transitive closure of type and proof". Optionally add an explicit `#assert_gamma_free OscInt.d4Limit`, since it passes (53 781 constants) and would make the S4.2 + S4.3 chain Gamma-free on record.

**NIT 5: garbled module docstring.**
`GammaFree.lean:11-18`: the module docstring contains a pasted `/-- … -/ theorem gammaProofControl … #assert_gamma_free_expect_fail gammaProofControl` inside an unclosed inline-code span. It compiles because Lean comments nest, but the prose is broken. *Fix:* end the sentence after `` `Real.Gamma_pos_of_pos` `` and refer to `gammaProofControl` by name.

**NIT 6: deprecation warning in the replay log.**
`OscInt/D4/LimitAssembly.lean:151` uses deprecated `if_neg` (warning in the replay log). It is harmless now but will break on a Mathlib bump. *Fix:* use `ite_eq_right` or `if_neg` per the hint.

**NIT 7: export-hash match is not tied to the config.**
`tools/src/bin/challenge.rs` (in `check`) accepts the export if *any* manifest line starts with `challenge-export {h}`, without checking that it is this config's line. This is not exploitable, because the config file hash and the Challenge sources are themselves bound to the manifest. *Fix:* match `challenge-export {h}  <config-stem>.ndjson`.

**NIT 8: from-source nanoda does not confirm the axiom set.**
The from-source nanoda in CI reports `1 pretty printer errors: ["Unable to print axioms"]`. The acceptance grep ignores this, so the from-source checker confirms type checking but not the axiom set. Other kernels and the audit cover the axioms. *Fix:* note this in the decision record, or check the axiom line when it prints.

**NIT 9: two statement-closure counts differ.**
Lesson 18 (`docs/lessons.md:114ff`) gives the statement closure as 33 099 after the fix, against referee B's independent 33 082. The 17-constant difference is not explained. *Fix:* one sentence on the counting convention.

## Prose check (overclaims)
- **No overclaim found.** `docs/decisions/2026-11-06-S4.md` is accurate: S4.1′ reuses every part, and `d4Bound_of` is derived from `d4BoundNe_of`.
- **Lesson 18** is candid.
- **STATUS rows 13-15** state the true status, "proved and replayed; post-proof review running", and stop short of "machine-checked as stated" pending post-proof review.
- **Open steps:** none of the three is "machine-checked as stated" per the README trust chain until the post-proof reviews are recorded.
