<!-- Adversarial review of S4.1 (fresh-context agent, prompt review/prompts/S4-adversarial.md), commit a776d28. Verbatim final report. -->

a776d28861175f299dfc2adff34661c892c945b9

# Adversarial review: S4.1 at a776d28

**Verdict.** I found no BLOCKER and no MAJOR. The type of `OscInt.d4Bound` is exactly the frozen constant `OscInt.Statements.D4BoundStatement`, and it uses only `propext`, `Classical.choice` and `Quot.sound`. The statement matches `docs/statements.md` S4.1, its hypotheses can be met by real phases, and its bound has bite. The trust chain holds together. What remains wrong is in the prose: several documents are out of date or slightly overstated. Status "proved and replayed; post-proof review pending" (`docs/STATUS.md:12`) is accurate. Once the post-proof reviews return FAITHFUL, the claim "machine-checked as stated" is supported.

## What I ran
All runs were `nice -n 10 lake env lean`, one at a time. Scratch files are in `/tmp/adv4/`; I wrote nothing in the repository.
- **`/tmp/adv4/Probe1.lean`:**
  - `#print axioms` for `OscInt.d4Bound`, `OscInt.fold` and `OscInt.nonStationary` each gives `[propext, Classical.choice, Quot.sound]`.
  - `(OscInt.d4Bound : D4BoundStatement)` checks.
  - The theorem specialises to φ = x³ + y³.
  - `-(2:ℝ)/3 = -(2/3)` holds, and t^{-2/3} < 1 for t > 1.
  - Consequence proved: for every admissible A, ‖∫e^{it(x³+y³)}A‖ → 0 as t → ∞.
- **`/tmp/adv4/Probe2.lean`:** I proved `ampBound_exists_delta`: for every δ > 0 there is A with `AmpBound 2 (closedBall 0 δ) A M` and A 0 = 1. So the δ that `d4Bound` produces always admits a nonzero amplitude. On the x³ + y³ instance this gives an A ≠ 0, the bound for all y and t ≥ 1, and 0 ≤ C·M.
- **`/tmp/adv4/Probe3.lean`:** `¬ FoldOrNondeg (x³+y³) 0`. S3 cannot be applied at the D4 point, so S4.1 is not a disguised corollary of S3.
- **Bite (numerics, x³ + y³ with a product bump, A(0) = 1):** t^{2/3}|I(t)| is 2.4074, 2.3940, 2.3923 and 2.39224 at t = 10, 10², 10³, 10⁴. This converges to Γ(1/3)²/3 = 2.392237, the brief's constant Γ(1/3)²/(√3|Disc|^{1/6}) with Disc = −27.
  - So −2/3 is the sharp exponent: no faster decay holds.
  - The bound is not implied by the trivial O(M) bound.
  - The 1D factor with a linear term (y ≠ 0) stays bounded (at most 4.6 after scaling by t^{2/3}), which is consistent with uniformity in y.
- **`lake env lean StatementTypes.lean`:** `TYPE-OK OscInt.d4Bound : OscInt.Statements.D4BoundStatement`.
- **Hashes:** `sha256sum` of `OscInt/Statements/D4.lean`, `OscInt/Statements/StationaryPhase.lean`, `Challenge/D4.lean` and `comparator-S4.json` matches stamp `20261106T033706Z-63564a8d78cd/manifest.txt`. The `build/commit/commitments.txt` D4 line `5205ebc0…` equals the stamped commitment. The round-2 calibration files and `key.json` match the hashes registered in `docs/calibration.md`.

## Attack results (no finding)
- **Statement against the docs.**
  - Quantifier order (`∃ δ > 0, ∃ C` after φ, before A, M, y, t) is as documented.
  - `ContDiff ℝ 4` is required, so `fderiv` of a non-differentiable function never occurs.
  - The `ddd` argument order in `cubicCoeffs` and the `disc` formula and sign are correct. `x³+y³ ↦ −27` (one real factor, D4⁺) and the generic (1, 2, 3, 5) case are checked in `OscInt/D4/Sanity.lean`.
  - `Real.rpow` is used with t ≥ 1. The integrand is continuous with compact support, so the Bochner integral is never 0 by convention.
  - There is no hidden ∇φ(0) = 0 hypothesis.
- **Ill-conditioned regimes.**
  - As Disc → 0 the constant may blow up; this is allowed because φ is fixed first.
  - |y| → ∞ is covered by S2.1 on large p (D6).
  - Amplitude support touching ∂B̄(0, δ): `sum_pieces` gives a partition of 1 on the closed ball, with δ = ε₀.
  - t near 1 is harmless.
- **Proof route.**
  - `OscInt/D4/Assembly.lean` calls `OscInt.fold` and `OscInt.nonStationary`, the proved theorems whose types are the frozen statements. It uses S3 with Λ = Icc 0 ε₀, K = annulus, K′ = B̄(0, G), and S2.1 with N = 1, c = 1.
  - `Final.lean` takes the frozen constant as its type.
  - No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `set_option`, macro or elab appears in `OscInt/D4/*`, `Blueprint/D4.lean` or `OscInt/Statements/D4.lean`.
  - A blueprint loophole could not affect soundness, because the final type is fixed and every part is a proved theorem.
- **Trust chain.**
  - `comparator-S4.json` names only `OscInt.d4Bound`, with no solution-supplied definitions and the standard three axioms.
  - The challenge export hash matches the stamp.
  - The replay record is for a0b1fde. Only documentation changed between a0b1fde and HEAD (`git diff --stat`), so the record is valid for the Lean content.
  - The stamp (03:37) and the pre-proof reviews (03:41) predate the first proof commits (from 05:54).
  - CI run 42172708736 on a0b1fde is green.

## Findings

**MINOR 1. `README.md:15` (and `:5`) understates the S4 status, and line 5 overclaims the scope.**
- Line 15 still says "S4 D4 | not started" while `docs/STATUS.md:12` says proved and replayed.
- Line 5 describes the library as having "the uniform D4 estimate t^{-2/3} with its limit constant (S4)", but S4.2 is not even stated.
- Failure scenario: a reader of the README sees no S4 result, or believes the limit constant is formalised.
- Fix: row "S4.1: proved and replayed, post-proof review pending; S4.2: not stated (owner decision)"; on line 5, mark the limit constant as planned.

**MINOR 2. `docs/HANDOFF.md:10-14, 31-34` are stale.**
- Line 11 says S4.1 has "no proof yet".
- Line 12 points to the route in `docs/statements.md`; the refereed route is now in `docs/proof-S4.md`.
- Line 14 cites calibration round 1 only; round 2 is scored.
- Lines 31-34 list "S4.1 proof" and "Calibration round 2" as next steps; both are done.
- Failure scenario: a fresh session re-does finished work or misreports the status.
- Fix: update for a0b1fde / a776d28 (S4.1 proved, verify-all PASS 8/8, calibration 8/8 pooled, post-proof reviews pending).

**MINOR 3. `docs/calibration.md:3-4, 127-131` overstate what the calibration measures.**
- Line 4 says referees were "given the standard pre-proof prompt". In fact rounds 1 and 2 used `calibration-r1.md` and `calibration-r2.md`. The real S4 review used `S4-pre-proof.md`, which points to the very sites (`ddd` order, `disc` sign) where V5's error was planted.
- "The miss rate per error is below 37% at 95% confidence" treats 8 hand-chosen plants, from two rounds with different prompts and file lengths, as one i.i.d. sample.
- The arithmetic is right: 0.025^{1/8} = 0.631, and 1 − 0.025^{1/4} = 0.602.
- Fix:
  - Name the prompts actually used.
  - Qualify the reading as "if the plants are regarded as exchangeable draws from these four kinds". The rate does not transfer to the S4-specific prompt or to errors of other kinds.

**MINOR 4. `review/2026-11-06-S4-pre-proof-answers.md` accepts a NIT that was never acted on.**
- The NIT "amplitudes for every δ" is accepted, but no such theorem exists: `OscInt/D4/Sanity.lean` covers only the mixed coefficients and the D4⁻ exclusion.
- The existing `sanity_ampBound_exists` covers only δ = 1, whereas S4.1's δ is chosen by the prover.
- Failure scenario: the non-vacuity of the amplitude class for the δ actually produced rests on prose.
- Fix: add the `ampBound_exists_delta` lemma from `/tmp/adv4/Probe2.lean` (a `ContDiffBump` with radii δ/2 and δ; it compiles) to a sanity file outside the stamped statement file.

**NIT 5. `docs/STATUS.md`: no prose paragraph for S4 and no CI citation.**
- S1 and S2/S3 each have an evidence paragraph; S4.1 has only the table row.
- The green CI run on a0b1fde (42172708736) is not cited.
- Fix: add a short S4 paragraph citing the record and the CI run.

**NIT 6. The post-proof prompt names the wrong commit.**
- `review/prompts/S4-post-proof.md` step 3 says `build/commit/commitments.txt` was "computed by the lead's make verify-all on this commit". It was computed on a0b1fde, not HEAD a776d28.
- This is harmless because only docs differ, but a referee could flag it.
- Fix: say "on a0b1fde (HEAD differs in docs only)".

**NIT 7. `docs/proof-S4.md:43-44` cites an unrecorded check.**
- The numerical check of D3 ("20 000 random (q, z)") was a throw-away script and is not in the record.
- This is harmless because D3 is proved in Lean.
- Fix: drop the sentence or label it "unrecorded, not evidence".

**NIT 8. A blueprint docstring contradicts the adopted revision.**
- The `CutoffFacts` docstring in `Blueprint/D4.lean` still suggests "bumps nonincreasing in |x|".
- `docs/proof-S4.md`'s revision note says D7 needs no monotonicity of the bump.
- Fix: make the docstring and the revision note agree.

**NIT 9. The newest pin line is not timestamped.**
- `stamps/pins.txt` is not covered by any stamp for its newest line, since it was pinned after the stamp. Its integrity rests on git history.
- This is by design, but it is not written next to "What stays trusted" in the README.
- Fix: one sentence in the README.

**NIT 10. The scope understates what is proved.** The Lean route uses only `disc ≠ 0` (`hdisc.ne` in `d4Bound_of`; `CubicGaugeFacts` is stated for `disc ≠ 0`). So the elliptic case D4⁻ is essentially already proved. This is recorded as owner option 3 in HANDOFF; no change is needed unless the owner widens the statement.

## Files
- `/home/user/lean-oscillatory/OscInt/Statements/D4.lean`
- `/home/user/lean-oscillatory/OscInt/D4/Final.lean`
- `/home/user/lean-oscillatory/OscInt/D4/Assembly.lean`
- `/home/user/lean-oscillatory/OscInt/D4/Sanity.lean`
- `/home/user/lean-oscillatory/Blueprint/D4.lean`
- `/home/user/lean-oscillatory/docs/proof-S4.md`
- `/home/user/lean-oscillatory/comparator-S4.json`
- `/home/user/lean-oscillatory/stamps/pins.txt`
- `/home/user/lean-oscillatory/StatementTypes.lean`
- `/home/user/lean-oscillatory/Axioms.lean`
- `/home/user/lean-oscillatory/docs/replay/2026-11-06-S4-verify-all.txt`
- `/home/user/lean-oscillatory/docs/STATUS.md`
- `/home/user/lean-oscillatory/docs/HANDOFF.md`
- `/home/user/lean-oscillatory/docs/calibration.md`
- `/home/user/lean-oscillatory/README.md`
- Scratch probes: `/tmp/adv4/Probe1.lean`, `/tmp/adv4/Probe2.lean`, `/tmp/adv4/Probe3.lean`
