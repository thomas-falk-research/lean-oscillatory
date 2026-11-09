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
`‖∫ e^{imΦ} A‖ = ℓ(∫ e^{imΦ} A) = ∫ e^{imΦ} (ℓ ∘ A)` (`ContinuousLinearMap.integral_comp_comm`, which needs `k ↦ e^{imΦ(k)} • A(k)` integrable; under the frozen hypotheses,
`A` continuous with compact support, it always is, so the junk-value branch (Bochner integral `0`) cannot occur; if it
did, the bound would still need `C · M · r(m) ≥ 0`, which holds because the scalar statement at `A = 0`, `M = 1` forces
`C ≥ 0`; adversarial review m6), and `ℓ ∘ A` is a scalar amplitude with
`tsupport (ℓ ∘ A) ⊆ tsupport A`, `C²`, and `‖D^j(ℓ ∘ A)‖ ≤ ‖ℓ‖ ‖D^j A‖ ≤ M`
(`ContinuousLinearMap.iteratedFDeriv_comp_left`, `norm_compContinuousMultilinearMap_le`; `ℓ` restricted to `ℝ`-scalars
for the real derivatives: `(ℓ.restrictScalars ℝ).norm_iteratedFDeriv_comp_left` and
`ContinuousLinearMap.norm_restrictScalars`, checked to compile by the adversarial referee). Every frozen statement of the form "∃ C, ∀ A M …, ‖∫ e^{imΦ} A‖ ≤ C · M · r(m)" with `C`
independent of `A` (all of S2.1–S3, FE-*, GD-*, the D4 bounds) therefore transfers to `E`-valued amplitudes with the
same constant. PROVEN since: batch VT (`OscInt/Front/VectorParts.lean`, `VectorFinal.lean`; replay of d261c19).

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

## 4. Result of the pre-registered classification (2026-11-08)
`docs/prereg/2026-11-08-VV-classify.md` (registered 226afd6, program 33b0848 committed before its run), output
`numerics/results-classify-vv-2026-11-08.txt` (first run, 2.8 s). Derivative self-test ok for every phase (Hessian
≤ 2.7e−9, third derivatives ≤ 1.4e−5 relative). Controls discriminate: C is CUSP with its X point at the origin; the
separable trap S(0.5) is CUSP (3434 X points along its critical curve), not NFD4. Verdicts:
- Q(1): CUSP (cusps at (−π, 0), (0, −π); a Hessian-zero point at (−π, −π) where the whole 3-jet vanishes (every third
  derivative of P carries a sine factor): the band minimum, not D4, with local rate at worst `t^{−1/2}`);
- Q(0.5): CUSP (8 cusp points, e.g. (−π, ±2π/3));
- **Q(3): NFD4, with no Hessian-zero point at all**: every point nondegenerate or a fold, `minfold` = 0.158;
- T (triangular lattice): CUSP (6 cusp points, e.g. (−π/2, −π/2)): the planned scalar fallback is *not* covered by GD.
Decision (rule fixed in the registration): the acceptance model is **QWZ at m = 3**. Since it has folds only, GD-F
applies and the expected rate is `t^{−5/6}` uniformly in `x` (CONJECTURED: numerics only; m = 3 is the topologically
trivial gapped phase, which does not matter for dispersion). The Lean classification of Q(3) (nondegenerate or fold at
every point of the torus) is the main risk of batch VV. Scope (adversarial review m2): Q(3) has folds only, so batch VV
will exercise GD-F, not the D4 branch (GD-C, GD), on a non-separable symbol; it is the near-separable regime in which
the `c₁c₂/m` term resolves the umbilics of `c₁ + c₂` into folds.

## 5. The QWZ m = 3 decay check failed its rate criterion (2026-11-08) — the model choice must be revisited
`docs/prereg/2026-11-08-VV-qwz-decay.md` (registered badacd3, program committed before its run), output
`numerics/results-qwz-decay-2026-11-08.txt`: **NOT PASS**. Over t ∈ [8, 64] the kernel decays like t^{−2/3}
(slope −0.654; t^{2/3} sup_x ‖G‖ flat between 17.2 and 18.9), not t^{−5/6}; the controls were distinguished (lattice
Laplacian −0.673, separable trap −0.403); accuracy 2e−14.
Diagnosis (lead, scratch computation after the run, not pre-registered; PLAUSIBLE until checked independently):
Q(m) for m > 2 is near-separable. On the diagonal k₁ = k₂ = a the Hessian entries H₁₁ and H₁₂ of ω vanish at nearby
but distinct points (m = 3: a ≈ 1.9045 and 1.9329; there ‖D²ω‖ ≈ 0.0065), and the value of H₁₂ where H₁₁ = 0 tends to
0 as m grows (0.063 at m = 2.05, 0.0065 at 3, 0.0013 at 4, 3.2e−5 at 8): the D4 points of c₁ + c₂ are split into folds
with a tiny margin. So the classification "nondegenerate or fold everywhere" can be true while the fold estimate's
constant is so large that t^{−2/3} is what is seen at every computed time; t^{−5/6} would only appear at very large t.
Consequences:
- No t^{−5/6} statement for QWZ is frozen.
- A t^{−2/3} bound (GD with D = ∅, or GD-F weakened) is consistent with the numerics, but its Lean proof needs the same
  classification of Q(3) on the whole torus, now known to have near-degenerate points (margins of order 1e−2 in the
  Hessian), which makes certificates delicate.
- Q(m) for m > 2 never has an exact D4 point on the diagonal (the gap above stays positive), so QWZ does not give a
  non-separable test of GD's D4 branch either.

## 6. ERRATUM (2026-11-09): QWZ m = 3 has exact cusp points; §4's verdict and §5's diagnosis are retracted
Found by the VT adversarial referee (`review/2026-11-09-VT-adversarial.md`, M1), confirmed by the lead.
- **Exact argument.** ω is symmetric under k₁ ↔ k₂, so at (a, a): H₁₁ = H₂₂, T₁₁₁ = T₂₂₂, T₁₁₂ = T₁₂₂. Where
  H₁₁(a) = H₁₂(a), det H = 0 with kernel spanned by (1, −1), and T[v, v, v] = T₁₁₁ − 3T₁₁₂ + 3T₁₂₂ − T₂₂₂ = 0
  identically: the point is neither a fold nor a D4 point. For m = 3, H₁₁ − H₁₂ changes sign on the diagonal at
  a = 1.910633 (lead's recomputation: H₁₁ = H₁₂ = 5.0886e−3, det H ≈ 3e−18, T[v, v, v] = 0, T₁₁₁ = 0.94); by evenness in
  each variable there are four such points (±a, ±a). The referee found the same at m = 2.05, 4, 8 and a linear vanishing of
  the fold quantity along the degenerate curve (a Whitney cusp, generically A₃, local rate t^{−3/4}).
- **Why the classifier said NFD4.** Grid spacing 2π/2048 ≈ 3.1e−3; its smallest fold quantity, 0.158, was about 1e−3 from
  the cusp, and its Newton search only starts below 1e−2 (`numerics/src/bin/classify_vv.rs`). A sub-grid cusp is invisible
  to it; the P1 cusp control did not test this case. The NFD4 verdict for Q(3) (§4) is a grid artifact.
- **§5 retracted.** "The classification can be true while t^{−5/6} appears only at very large t" is false: the asymptotic
  rate is at best t^{−3/4}, and no proved theorem in the repository (GD, GD-F, GD-C) applies to Q(m), m > 2. The lead's
  diagnosis checked the wrong condition (H₁₂ where H₁₁ = 0, instead of H₁₁ = ±H₁₂).
- **Also:** criterion (b) of `docs/prereg/2026-11-08-VV-qwz-decay.md` could not discriminate (adversarial m3: for a
  t^{−2/3} decay the ratio is 8^{1/6} ≈ 1.41, for t^{−1/2} it is 2, both below 3), and there was no positive control
  decaying like t^{−5/6}.
- **Consequences.** QWZ (m > 2) is dropped as an acceptance model. No acceptance model for VV exists now. A future search
  must check symmetry lines and refine near small fold quantities, with a sub-grid positive control (lessons 43).
