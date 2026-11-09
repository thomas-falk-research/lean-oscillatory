7218811a8a6eb2fd8e0e2b8aaf8e7bb38f6e1bb0 (`git rev-parse HEAD` gives 7218811…; the repository tree is clean, and from a1d2a64 to HEAD only the replay record and two prompts were added, with no Lean changes)

# Post-proof referee A: batch LE (T0E, T6F, T6E)

**Overall verdict:** all three theorems are FAITHFUL to `docs/statements.md` ("Batch LE", with clarifications 6–9), at full scope. There is no BLOCKER and no MAJOR. Two MINOR findings concern the documentation and evidence record, not the mathematics.

**What I ran** (scratch only, `/tmp/postA/Check.lean`; nothing written in the repository; one `nice -n 10 lake env lean` at a time; no `make` and no `lake build`):
- I recomputed SHA-256 hashes against the stamp manifest.
- I checked the three RFC 3161 tokens of `stamps/20261108T160847Z-4a183530559f` myself with `openssl ts -verify` against `stamps/roots`: freetsa, digicert and sectigo all return OK, time 16:08:50Z.
- I compiled a check file against the built `OscInt`.

## (1) Is each type exactly the frozen constant?
- **Stamped file.** `OscInt/Statements/LatticeExplicit.lean` has SHA-256 `c2016339…7f9187f` at HEAD. This equals the entry in `stamps/20261108T160847Z-4a183530559f/manifest.txt` and the file at 4a18353. `git diff 4a18353 HEAD` shows no change under `OscInt/Statements/`, `Challenge/` or `comparator-LE.json`.
- **StatementTypes.lean** (lines 73–75): `#assert_type_is` holds for `OscInt.API.latticeKernel1Explicit`, `latticeKernelFactor` and `latticeLaplacianExplicit` against the three frozen constants.
- **Replay record** `docs/replay/2026-11-08-session7-LE-verify-all.txt`:
  - lines 123–125 are the three TYPE-OK lines;
  - line 461 shows comparator-LE.json accepted against the LE stamp;
  - line 76 shows the axiom audit at 940 of 940;
  - leanchecker passes on all LE modules (lines 188–191, 207, 233);
  - RESULT PASS, 9 of 9 steps, on a1d2a64.
- **Independently:**
  - `example : …Statement := …` compiles for all three.
  - `#print axioms` on each gives only `[propext, Classical.choice, Quot.sound]`.
  - `Challenge/LatticeExplicit.lean` declares the same three names with `sorry`.
  - comparator-LE.json lists exactly these three names. `definition_names` is empty, as in comparator-GD.json; the challenge imports the same statements module.

## (2) Fidelity to the docs
I checked the Lean text against the docs mechanically. In my file, an `↔` between `LatticeKernel1ExplicitStatement` and the docs formula holds:
- the formula is written out as `∫ k in (-π)..π, exp(↑(t cos k + ξ k) · I)` and `24·2^{1/4} t^{-(1/2)} + 36·2^{1/6} t^{-(1/3)}`;
- the proof is `unfold` plus `norm_num [neg_div]`;
- this confirms that `-(1:ℝ)/2` is `−1/2`.

For T6F, the unfolded statement over `Icc ×ˢ Icc` is accepted by `Iff.rfl`.

| | Docs | Lean | Verdict |
|---|---|---|---|
| T0E | for t > 0 and real ξ, \|I(t, ξ)\| ≤ A t^{−1/2} + B t^{−1/3}, with A = 24·2^{1/4} and B = 36·2^{1/6} | `∀ t ξ : ℝ, 0 < t → ‖latticeKernel1 t ξ‖ ≤ …`; `latticeKernel1` is the oriented interval integral over [−π, π] of exp(i(t cos k + ξk)) | **FAITHFUL, full**. ξ real is item 1 of the docs; t > 0 is item 2. |
| T6F | for every real t and x ∈ ℤ², K(t, x) = I(t, x₁) I(t, x₂) | `∀ (t : ℝ) (x : ℤ × ℤ), latticeKernel t x = latticeKernel1 t x.1 * latticeKernel1 t x.2`; `latticeKernel` is the batch-GD kernel, unchanged | **FAITHFUL, full** (no restriction on t) |
| T6E | for t ≥ 1 and x ∈ ℤ², \|K\| ≤ (A + B)² t^{−2/3} | `∀ t x, 1 ≤ t → ‖latticeKernel t x‖ ≤ (A + B)^2 * t^(-(2:ℝ)/3)` | **FAITHFUL, full** |

**Numbers in the docs, recomputed:**
- A = 28.5410, B = 40.4086, (A + B)² = 4754.05.
- The T0E right side falls below 2π for t > 518.525.
- T6E falls below 4π² for t > 1321.47.
- (A + B)²/B² = 2.911.
- (2π)^{−2}(A + B)² 2^{−2/3} = 75.86.

All match clarifications 6, 8 and 9.

I also compiled clarification 8's direct composition, |K| ≤ (A t^{−1/2} + B t^{−1/3})² for t > 0, from the two proved theorems. It goes through in four lines.

## (3) Non-vacuity
- The hypotheses (0 < t, 1 ≤ t) can obviously be satisfied, so none of the theorems can be vacuous.
- I fed the proved theorems into all six sanity theorems of `OscInt/Front/LatticeExplicitSanity.lean`, and all six compile:
  - `latticeKernel1Explicit_eight` at t = 8 and `_eighth` at t = 1/8;
  - `latticeKernelFactor_neg` at t = −2 and `_generic` at t = 3;
  - `latticeLaplacianExplicit_one` at t = 1 and `_diag` on x = (n, n).
- That composition exists in no committed, compiled file, though. See MINOR-1.

## (4) What the proof rests on
- `latticeKernel1Explicit = t0e_of leAngle lePiece2 lePiece3`.
- `lePiece2` and `lePiece3` apply `OscInt.vanDerCorput_two` and `OscInt.vanDerCorput_three`. These are TYPE-OK against the frozen `VdC2Statement` and `VdC3Statement` (StatementTypes lines 29–30; replay lines 79–80). They are instantiated with:
  - φ = t cos, μ = t·2^{−1/2}, ψ = 1 (via `sanity_amplitude_one` in the frozen `OscInt/Statements/VanDerCorput.lean`), p = ξ.
- `t6f` uses Fubini through Mathlib's `setIntegral_prod_mul`.
- `t6e_of` uses only T0E, T6F and rpow monotonicity.
- The internal blueprint propositions (`Blueprint/LatticeExplicit.lean`: `LEAngleFacts`, `LEPiece2Facts`, `LEPiece3Facts`) are proved, not assumed. Since the final types are checked against the frozen constants and the axioms are clean, what those intermediate statements say does not affect correctness.
- There is no `sorry` and no hypothesis threaded through the final theorems (`OscInt/Front/LatticeExplicitFinal.lean` lines 24–32).

## (5) Order and documentation claims
- **Statements frozen before review.** Commit 4a18353 has a manifest bound by RFC 3161 tokens at 16:08:50Z (verified ×3 by me). The manifest contains no LE proof file.
- **Reviews stamped before any proof.** The reviews and answers are stamped in `stamps/20261108T164514Z-c91a9a8bb0b6`: 16:45:19Z per the replay, line 690ff. That manifest contains no `LatticeExplicitParts` or `Final` file.
- **Proofs appeared afterwards.** The route referee saw the parts file appear untracked at 16:57.
- So the claim "frozen and blind-reviewed before any proof" is supported to the usual extent. The usual caveat: the stamps show the proofs were not *in the tree* by 16:45:19Z. They cannot exclude drafts kept outside the repository.
- **Route-review order.** This order was not kept, and the docs say so plainly:
  - `docs/proof-LE.md` lines 35–41 ("Revision after the route referee", M1);
  - lesson 42 in `docs/lessons.md`;
  - the commit message of a1d2a64.
  I found no document that still claims "route reviewed before any part was proved" for LE.
- **Sanity file.** It changed between the statement stamp (hash cfc8…) and the review stamp (hash d85b…; HEAD matches d85b…). The changes are the answers to the reviews, inside the review stamp, so this is consistent with the docs.
- **Clarifications 6–9.** They were added after the reviews and change no statement text, as they say.

## Findings

**BLOCKER:** none.

**MAJOR:** none.

**MINOR-1. No committed consumer check feeds the LE theorems into their sanity theorems.**
- Files: `examples/consumer/` (Makefile lines 81–86) and `OscInt/Front/LatticeExplicitSanity.lean`.
- For GD, `examples/consumer/ConsumerLattice.lean` lines 54 and 64 apply `GlobalSanity.*` to the proved `OscInt.API.*` theorems. No file does this for LE. The only LE use is `examples/api/Snippets.lean` lines 192ff, which is `example : Stmt := thm` with no data.
- Non-vacuity is not actually at risk (see (3)), and I compiled the six compositions. Still, part (3) of the brief asks for a compiled use on real data, and the repository does not contain one.
- Fix: add the six lines from `/tmp/postA/Check.lean` to a consumer file run by `make`.

**MINOR-2. `docs/prior_art.md` lines 50–51 claim more than the trust chain supports.**
- The lines say "the factorisation is machine-checked by batch LE (statement T6F)".
- They were written in 0a7409d at 15:34Z, before the LE statements existed (4a18353, 15:49Z). At HEAD the proof and replay exist, but the post-proof blind reviews (this review) are not yet in.
- Under the rule in `docs/STATUS.md` lines 3–4, "machine-checked" needs every row of the trust chain, so the claim is still premature.
- `docs/STATUS.md` has no LE rows at all, which avoids the problem by staying silent.
- Fix: once the post-proof reviews are committed, add T0E, T6F and T6E rows to STATUS. Until then, reword prior_art to say "proved and replayed (a1d2a64); post-proof review pending".

**NIT-1.** `docs/proof-LE.md` line 5 points to `/tmp/lead/Names.lean` for the name checks. The revision (line 44) fixes this through `MathlibNames.lean`, but the stale pointer in line 5 remains.

**NIT-2.** The replay is of a1d2a64, not HEAD. That is acceptable, because a1d2a64..HEAD touches no Lean file (`git diff --stat`: only the replay text and two prompts). The docs should say "replay of a1d2a64" when they cite it, as the GD rows do.

**NIT-3.** The git author dates are not monotone around the review stamp: 44477fe, dated 16:36Z, sits after 9984c8d, dated 16:45Z. This does not concern LE files. It is a reminder that only the RFC 3161 tokens are evidence of time, not git dates.

## Files examined
- /home/user/lean-oscillatory/docs/statements.md (Batch LE, lines ~505–559)
- /home/user/lean-oscillatory/OscInt/Statements/LatticeExplicit.lean
- /home/user/lean-oscillatory/OscInt/Front/LatticeExplicitFinal.lean, LatticeExplicitParts.lean, LatticeExplicitAssembly.lean, LatticeExplicitSanity.lean
- /home/user/lean-oscillatory/Blueprint/LatticeExplicit.lean
- /home/user/lean-oscillatory/StatementTypes.lean, comparator-LE.json, Challenge/LatticeExplicit.lean
- /home/user/lean-oscillatory/docs/replay/2026-11-08-session7-LE-verify-all.txt
- /home/user/lean-oscillatory/docs/proof-LE.md, review/2026-11-08-LE-route-referee.md, review/2026-11-08-LE-pre-proof-answers.md
- /home/user/lean-oscillatory/docs/STATUS.md, docs/prior_art.md, docs/lessons.md

Scratch check file: /tmp/postA/Check.lean. It compiles cleanly. It covers:
- the type checks and the docs-formula `↔`;
- the six sanity compositions;
- the clarification-8 corollary;
- `#print axioms`.
