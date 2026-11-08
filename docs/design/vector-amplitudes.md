# Design: vector-valued amplitudes (batch VV) and a non-separable two-band model

Status: design draft, 2026-11-08 (session 7, lead). Nothing here is frozen or proved. Labels: PROVEN (machine-checked),
VALIDATED (checked in this session, how stated), CONJECTURED, PLAUSIBLE.

## 1. Route: duality, not a port
The spike (grep over `OscInt/VanDerCorput`, `StationaryPhase`, `D4`, `Front`, about 12.9k lines) found no real-part,
conjugation or `Complex.abs` step in the proofs; amplitudes enter through `*` and `integral_mul_*`. A port of the
proofs from `ℂ` to a Banach space `E` is therefore PLAUSIBLE-mechanical but large. A shorter route avoids touching any
proof:

For `E` a complex Banach space and `A : ℝ² → E`, and `ℓ ∈ E*` with `‖ℓ‖ ≤ 1` and `ℓ(∫ e^{imΦ} A) = ‖∫ e^{imΦ} A‖`
(Hahn–Banach, Mathlib `exists_dual_vector''`):
`‖∫ e^{imΦ} A‖ = ℓ(∫ e^{imΦ} A) = ∫ e^{imΦ} (ℓ ∘ A)` (`ContinuousLinearMap.integral_comp_comm`, which needs `A`
integrable; otherwise the Bochner integral is `0` and the bound is trivial), and `ℓ ∘ A` is a scalar amplitude with
`tsupport (ℓ ∘ A) ⊆ tsupport A`, `C²`, and `‖D^j(ℓ ∘ A)‖ ≤ ‖ℓ‖ ‖D^j A‖ ≤ M`
(`ContinuousLinearMap.iteratedFDeriv_comp_left`, `norm_compContinuousMultilinearMap_le`; `ℓ` restricted to `ℝ`-scalars
for the real derivatives). Every frozen statement of the form "∃ C, ∀ A M …, ‖∫ e^{imΦ} A‖ ≤ C · M · r(m)" with `C`
independent of `A` (all of S2.1–S3, FE-*, GD-*, the D4 bounds) therefore transfers to `E`-valued amplitudes with the
same constant. PLAUSIBLE (paper argument above; the Mathlib names were found by grep at the pin, not yet used).

Consequences for the batch: the VV statements are new frozen constants (GD-V, GD-F-V, GD-N-V, FE-S4.1′L-V at least),
each with `E` universally quantified over `[NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]`; the scalar
statements stay untouched; the scalar case of a VV statement is the instance `E = ℂ` (a corollary, as the session-7
order asks). One generic transfer lemma, then a few lines per statement.

## 2. The acceptance model must be non-separable and classifiable
The owner's acceptance test is a non-separable two-band model compiled end to end. The hard part is the
classification of the band function (nondegenerate / fold / finitely many D4 points) in Lean, not the vector-valued
amplitude.

**A trap (CONJECTURED, to be checked numerically before anything is frozen).** The gapped model
`H(k) = ω₀(k) σ_z + m σ_x`, `ω₀ = cos k₁ + cos k₂`, has bands `±√(ω₀² + m²)`. Its gradient vanishes on the whole curve
`ω₀ = 0` (the factor `ω₀/√(ω₀² + m²)`), where the Hessian has rank 1 with kernel tangent to the curve and the band is
constant along it: neither fold nor D4. The decay is then worse than `t^{−2/3}` (PLAUSIBLE: `t^{−1/2}`, a
Morse–Bott-type critical curve), and GD does not apply. Any model whose band is a function of a separable symbol has
this problem.

**Candidate: the Qi–Wu–Zhang (QWZ) two-band model** (X.-L. Qi, Y.-S. Wu, S.-C. Zhang, Phys. Rev. B 74, 085308
(2006), citation from memory, not re-checked this session; a standard Chern-insulator model). `H(k) = sin k₁ σ_x + sin k₂ σ_y + (m + cos k₁ + cos k₂) σ_z`, bands `±ω`,
`ω² = 2 + m² + 2m(cos k₁ + cos k₂) + 2 cos k₁ cos k₂`, gapped for `m ∉ {0, ±2}`; the spectral projections
`P_±(k) = (1 ± H(k)/ω(k))/2` are smooth matrix-valued amplitudes. The `cos k₁ cos k₂` term makes it non-separable.
Its classification is unknown to us: CONJECTURED that for generic `m` (e.g. `m = 1`) every point is nondegenerate, a
fold, or one of finitely many D4 points. Plan:
1. Pre-register a numeric classification for `ω` at `m ∈ {1, 1/2, 3}` (the P1-classify program is the template), with
   controls (the trap model above must be reported as NOT classifiable).
2. If it passes: freeze the VV statements and a model statement (kernel `∫_{T²} e^{−itH(k) + ix·k} dk` bounded by
   `C t^{−σ}` uniformly in `x`, with `σ` from the classification), and prove the classification in Lean. The Lean
   classification is the risk (the arccos family's is still open, `docs/HANDOFF.md`); working with `ω²`, a
   trigonometric polynomial, may help.
3. If it fails: report it with the numbers, and fall back to the scalar triangular lattice `cos k₁ + cos k₂ +
   cos(k₁ + k₂)` for the non-separable test of GD, and the componentwise corollary for VV (the review's bridge).

## 3. Prior art to check before any claim
Dispersive estimates for two-band lattice models (graphene: Dirac points, not gapped; gapped Chern-insulator models)
in the analysis literature; any formalisation of vector-valued oscillatory integrals (roos-j's van der Corput is
Banach-valued in 1D, `docs/prior_art.md`). No novelty is claimed here.
