c98f4962f9fbf7d8158fc5b4acbb15d965885488

# GD post-proof review, referee A (fresh context)

`git rev-parse HEAD` = c98f4962f9fbf7d8158fc5b4acbb15d965885488. HEAD did not move. Nothing in the repository was
modified. Scratch files are under /tmp/ppA/. I ran one Lean process at a time, with `nice -n 10 lake env lean
-DautoImplicit=false`, against the build products already on disk (built at 12:35Z, after the 12:32Z header edits).

## Summary

All eight theorems (GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L) are **FAITHFUL, full scope** against `docs/statements.md`,
"Batch GD", together with its post-stamp clarification. There are no BLOCKER and no MAJOR findings. The MINOR and NIT
findings below are about how complete the evidence is, not about whether the statements are correct.

## 1. Type identity and freezing

- `StatementTypes.lean:65-72` asserts, with syntactic `Expr` equality, that each final theorem's type is the frozen
  constant. The replay record `docs/replay/2026-11-08-session6-GD-verify-all.txt` contains the 8 GD TYPE-OK lines
  (c62a621, verify-all PASS 9/9). I re-ran the same `#assert_type_is` elaborator at HEAD in /tmp/ppA/Check.lean and got
  8/8 TYPE-OK. `#print axioms` on all eight gives [propext, Classical.choice, Quot.sound].
- SHA-256 at HEAD equals the stamp manifest `stamps/20261108T094842Z-edf7787a2845/manifest.txt` for:
  - `OscInt/Statements/Global.lean` (edaaf9c6…);
  - `Challenge/Global.lean` (bfd5199d…);
  - `comparator-GD.json` (76172b5b…);
  - the imported statement files `Family.lean`, `Convert.lean`, `FrontEnd.lean` and `D4.lean`.
- `git diff edf7787 c98f496 -- OscInt/Statements Challenge comparator-GD.json` is empty.
- `stamps/pins.txt` pins all 8 constants and `challenge:comparator-GD.json` to that stamp.
- Replay: the commitments match the stamp for all 8; `comparator: comparator-GD.json accepted against
  stamps/20261108T094842Z-edf7787a2845` (line 554); the GD export SHA d64efded… matches the stamped manifest; the stamp's
  RFC 3161 tokens verified (freetsa, digicert, sectigo, all at 09:48:45Z).
- Between c62a621 and HEAD, every change to a `.lean` file is a comment header. I checked this with a diff of
  added/removed lines: only SPDX/copyright/author lines were added, and nothing changed in `OscInt/Statements/` or
  `stamps/`. The licence-headers record shows that all 11 challenge exports are byte-identical and that all 45
  commitments still match.

## 2. Fidelity, statement by statement (`OscInt/Statements/Global.lean` vs `docs/statements.md:418-493`)

| Thm | Lean | Verdict | Scope | Notes |
|---|---|---|---|---|
| GD-C | `OscInt.API.globalDecayCrit` | FAITHFUL | full | The quantifiers match the docs: Ψ, compact K, open U ⊇ K, compact K′, `Finset` D ⊆ U, `ContDiffOn ℝ 4 Ψ U`. The hypothesis covers critical points (`fderiv ℝ Ψ k + L = 0`) in K \ D for L ∈ K′. Every point of D satisfies `IsD4Point`. The conclusion is C·M·m^{-2/3} with C independent of A, M, L ∈ K′ and m ≥ 1. The amplitude (2, K, M) is exactly the docs' definition. Since U is open, `fderiv`/`iteratedFDeriv` of the global Ψ at points of U are the local derivatives. |
| GD | `OscInt.API.globalDecay` | FAITHFUL | full | The pointwise classification `Classified` is at every k ∈ K \ D. The bound holds for all L, as the docs say. By clarification (2) it is not stronger than the classical hypothesis. |
| GD-F | `OscInt.API.globalFold` | FAITHFUL | full | `FoldOrNondegMatrix` on all of K; m^{-5/6}; all L. |
| GD-N | `OscInt.API.globalNondeg` | FAITHFUL | full | `det (hessianMatrix Ψ k) ≠ 0` on K; `C * M / m`, which is the docs' m^{-1}. |
| SH | `OscInt.API.sharpness` | FAITHFUL | full | Both halves (the lower bound (‖c‖/2)m^{-σ} eventually, and no σ′ > σ with any C), for `ℝ → ℂ` and for `ℕ → ℂ`, as the docs state. |
| T1 | `OscInt.API.torusUnfold` | FAITHFUL | full | ∃ η, `ContDiff ℝ ∞` (smooth, not analytic), `tsupport ⊆ closedBall 0 4` in the sup norm on ℝ×ℝ. The identity holds for every continuous g that is 2π-periodic in each variable. |
| T6 | `OscInt.API.latticeLaplacianDecay` | FAITHFUL | full | `latticeKernel` is exactly the docs' K(t, x). ∃C ∀ t ≥ 1 ∀ x ∈ ℤ²: ‖K‖ ≤ C t^{-2/3}. |
| T6L | `OscInt.API.latticeLaplacianLimit` | FAITHFUL | full | n^{2/3}(−1)ⁿK(n,(n,n)) → `d4ClosedConstant (−1/48)` in ℂ. I proved independently in scratch that `d4ClosedConstant (−1/48) = Γ(1/3)²·48^{1/6}/√3` (/tmp/ppA/Check.lean, last example; it compiles). |

Hand checks of the mathematics behind the modelling:

- At (π/2, π/2), cos(π/2+κ) + (π/2+κ) = π/2 − κ³/6 + … has no linear term. The cubic part is (κ₁³+κ₂³)/6, so a = d = 1/6
  and disc = −27a²d² = −1/48, as stated.
- The folklore route agrees: (2π)²(−1)ⁿJₙ(n)² with Jₙ(n) ~ Γ(1/3)/(2^{2/3}3^{1/6}π n^{1/3}) gives
  Γ(1/3)²·2^{2/3}3^{−1/3}, which equals Γ(1/3)²·48^{1/6}/√3.
- Along x = (n, n) the only critical point of cos k + k in [−π, π] is k = π/2, as the modelling note says.

## 3. Non-vacuity on real data

- **T1, GD, T6.** `OscInt/Front/LatticeKernel.lean:89-102` proves T6 by applying GD (`globalDecay_of`) to the real
  phase cos k₁ + cos k₂ on K = B̄(0, 4), with a nonempty D (`latticeD4`) and the proved classification
  (`LatticeSymbol.latticeSymbolFacts`). It uses T1's explicit weight through `unfoldFacts`. GD's hypotheses, including
  the D4 points, are therefore discharged on genuine data inside the proof of T6.
- **Consumer example.** `examples/consumer/ConsumerLattice.lean` applies the proved theorems T6 (`dispersive`), T6L+SH
  (`not_faster`) and GD (`globalDecay_hyp OscInt.API.globalDecay`, x³+y³ on B̄(0,1), which has all three point types). I
  compiled a copy (/tmp/ppA/ConsumerLattice.lean, header stripped, body unchanged): no errors; `dispersive` and
  `not_faster` use only the standard axioms.
- **Sanity layer.** `OscInt/Front/GlobalSanity.lean` discharges every statement's hypotheses on real data through the
  constants:
  - `globalDecay_ell`, `globalDecayCrit_ell`, `globalDecayCrit_hyp_crit`, `globalDecay_hypShift` (D4 point at (1,1));
  - `globalFold_fold`, `globalNondeg_quad` (U = B(0,2) ≠ ℝ²);
  - `sharpness_sqrt`, `torusUnfold_moments`, `latticeLaplacianDecay_diag`, `latticeLaplacian_sharp`.
- I instantiated each of these sanity theorems with the actual proof (/tmp/ppA/Check.lean, `pA_*`). All compile, with
  the standard axioms.

## 4. Findings

- **MINOR. No compiled file in the repository applies the proved GD-C, GD-F or GD-N to concrete data.**
  `examples/api/Snippets.lean:160-172` only restates their types. GlobalSanity applies only the statement constants. The
  hypotheses are shown dischargeable there, so adding `globalFold_fold OscInt.API.globalFold` and the like is trivial;
  I did it in scratch and it compiles. Suggestion: add these three lines to `ConsumerLattice.lean` or a sanity file so
  the repository itself carries the evidence.
- **MINOR. The consumer example is not covered by the replay record.** `ConsumerLattice.lean` is compiled by
  `make quick` (`Makefile:85`; commit message of c62a621). It does not appear in the verify-all record, and
  `README.md:32` points readers to it. I compiled it myself (see §3).
- **MINOR. HEAD has not had a kernel replay.** The kernel and comparator replay is for c62a621. HEAD differs only by
  comment headers. The licence-headers record checks the challenge exports and commitments, but not a solution-side
  export or kernel replay, and it does not record a `lake build` exit status. This cannot affect any declaration, but
  `docs/STATUS.md:43-50` should keep citing the replay as being "on c62a621", as it does now, and not as being on HEAD.
- **MINOR. The statement-first order rests on timing that cannot be fully audited.**
  - The review stamp `20261108T102629Z-8c8d7b090adb` (RFC 3161, 10:26:32Z) comes before the first proof commit 2aae8dd
    (10:36:22Z), and that commit holds about 900 lines of proof.
  - `docs/HANDOFF.md:85` says the proof agents took 2–3 minutes each, which is consistent with this.
  - The only pre-existing Lean draft, `docs/design/torus-lattice/TorusDraft.lean.txt`, contains statements, plus one
    periodicity lemma.
  - Git cannot exclude uncommitted proof work before 10:26. This is a limitation of the evidence; I found no
    indication of a violation.
- **NIT.** The referee prompt names `LatticeLimitFinal.lean`; the file is `OscInt/Front/LatticeFinal.lean`.
- **NIT.** `OscInt/Front/GlobalSanity.lean:442` uses the deprecated `if_pos`, which shows up as a warning in every build
  log of the replay.
- **NIT.** The sanity theorems detect only plants that strengthen a hypothesis or weaken the conclusion. GlobalSanity
  says so for each theorem ("Not detected: weakening plants"). This is not a defect of the proved theorems: their types
  are syntactically the frozen constants, so a weakening plant would fail the TYPE-OK check and the commitments.

## 5. Claims in docs/STATUS.md and README.md

- `docs/STATUS.md:43-50` says "proved, replayed; post-proof review pending". This is supported: c62a621 verify-all
  PASS, and the commitments, comparator and stamps all verified.
- "7 kernel runs" is the project convention used throughout STATUS: per-module leanchecker, nanoda, con-leche, con-ron,
  lean4lean, and the Lean default and paranoid kernels in the comparator. The record has all of them.
- `README.md:32` defers to STATUS. Nothing it claims goes beyond the evidence.
- `docs/statements.md` clarification (1), the punctured-neighbourhood fold argument, is marked as argued on paper and
  not formalised. That labelling is accurate, and GD does not depend on it.
