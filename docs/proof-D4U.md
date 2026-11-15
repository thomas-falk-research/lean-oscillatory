# Route: batch D4U (S4.2U, S4.2O)

Lead, session 12, after the pre-proof reviews were answered (`review/2026-11-15-D4U-pre-proof-answers.md`) and stamped.
- **Blueprint:** `Blueprint/D4Uniform.lean`, one `…Facts` proposition per part.
- **Assembly:** in the same file, compiled before any part is proved:
  - `d4LimitUniform_of (hR : CommonRadiusFacts) (hL : LinearFacts) : D4LimitUniformStatement`;
  - `d4LimitOffset_of (hU : D4LimitUniformStatement) (hM : ModulationFacts) : D4LimitOffsetStatement`.

Disclosure (as in `docs/statements.md`, batch D4U): a hand proof of this shape existed before the freeze, in the
external packet, and referee B outlined the same reduction. The route below is the lead's.

## Why this route

S4.2U is the classical ε/2 argument: the stamped S4.1′ bounds `t^{2/3} |∫ e^{itφ} (A − b)|` by `C η` for an amplitude
difference with C² budget η, uniformly in t ≥ 1, and the stamped S4.2 gives the limit for each of the finitely many
centres b of an η-net. S4.2O is S4.2U applied to the modulation family `{e^{i y·κ} A : ‖y‖ ≤ R}`: the linear term
becomes part of the amplitude, and the value at 0 is unchanged. Rejected alternatives:
- **Re-proving the D4 limit with an offset** (a direct stationary-phase expansion with the term `y·κ`): longer, and it
  duplicates S4.2's proof.
- **Explicit Leibniz bounds for the modulation family** (`‖D^j(e_y − e_z)‖ ≤ L_j |y − z|` on K): needs the iterated
  derivatives of `κ ↦ exp(i y·κ)` in closed form; the compactness route below needs only joint smoothness.

## The parts

**P-radius `CommonRadiusFacts`.** For φ with `D4LimitPhase φ` there are δ > 0 and C ≥ 0 such that every amplitude with
`AmpBound 2 (B̄(0, δ)) A M` satisfies ‖∫ e^{itφ} A‖ ≤ C M t^{−2/3} for t ≥ 1, and t^{2/3} ∫ e^{itφ} A → c_C A(0).
- S4.1′ (`OscInt.d4BoundNe`) at y = 0 gives (δ₁, C₁); S4.2 (`OscInt.d4Limit`) gives δ₂. Take δ = min δ₁ δ₂ and
  C = max C₁ 0. A budget on the smaller ball is a budget on both larger balls (`Metric.closedBall_subset_closedBall`);
  `lin 0 κ = 0`; M ≥ 0 from the order-0 bound at any point (`norm_nonneg`), so `C₁ M ≤ C M`.

**P-linear `LinearFacts`.** For a continuous phase Q and two amplitudes with budgets on a compact K,
`oscInt2 Q (A − B) = oscInt2 Q A − oscInt2 Q B`.
- Each integrand is continuous with compact support (`Continuous.integrable_of_hasCompactSupport`;
  `HasCompactSupport` from `tsupport ⊆ K` and `IsCompact.of_isClosed_subset`); `MeasureTheory.integral_sub`.

**P-mod `ModulationFacts`.** For δ > 0, an amplitude with `AmpBound 2 (B̄(0, δ)) A M` and R, the family
`{fun κ => exp(i · lin y κ) · A κ : ‖y‖ ≤ R}` is `AmpTotallyBounded` on `B̄(0, δ)`.
- Budget of each member: the member is C² (`ContDiff.mul`, `Complex.contDiff_exp`, the linear map `lin y`), its
  `tsupport` lies in `tsupport A` (`tsupport_mul_subset_right`), and its derivatives of order ≤ 2 are continuous with
  compact support, hence bounded (`Continuous.bounded_above_of_compact_support`, as in `OscInt.API.ampBoundOfContDiff`).
- Net, by compactness: put F(y, κ) = exp(i lin y κ) A(κ) on (ℝ × ℝ) × (ℝ × ℝ); F is C² jointly. The slice derivative
  `iteratedFDeriv ℝ j (F (y, ·)) κ` equals the joint derivative composed with `inr` (the lemma
  `OscInt.API.FamilyAux.iteratedFDeriv_slice`, stated for real values; its proof is generic in the codomain, so a
  complex-valued copy is needed), hence is jointly continuous in (y, κ). For κ ∉ B̄(0, δ) it is 0
  (`support_iteratedFDeriv_subset`, since `tsupport (F (y, ·)) ⊆ tsupport A ⊆ B̄(0, δ)`). On the compact set
  `B̄(0, R) × B̄(0, δ)` each of the three slice derivatives (j = 0, 1, 2) is uniformly continuous
  (`IsCompact.uniformContinuousOn_of_continuous`), so there is ρ > 0 with
  ‖y − y′‖ < ρ ⇒ ‖D^j F(y, ·)(κ) − D^j F(y′, ·)(κ)‖ ≤ η for all κ ∈ B̄(0, δ) and j ≤ 2; off the ball both vanish.
  The derivative of the difference is the difference of the derivatives (`iteratedFDeriv_sub_apply`), so
  `AmpBound 2 (B̄(0, δ)) (F(y, ·) − F(y′, ·)) η`. A finite ρ-net of `{y : ‖y‖ ≤ R}` drawn from that set (compact:
  `IsCompact.elim_finite_subcover` on the balls `ball y ρ`, or `finite_cover_balls_of_compact`) gives the finite subset.

## The assembly

**S4.2U from P-radius and P-linear.** Fix φ; take δ, C from P-radius. Given a family S with
`AmpTotallyBounded (B̄(0, δ)) S` and ε > 0, put η = ε / (2 (C + |c_C| + 1)) and take a finite η-net F ⊆ S. Each b ∈ F
has a budget (first conjunct), so by P-radius `t^{2/3} I(b) → c_C b(0)`; finitely many limits give one T₀ with
‖err_b(t)‖ < ε/2 for t ≥ T₀ and all b ∈ F (`Filter.eventually_all_finite`). Let T = max T₀ 1. For A ∈ S choose b ∈ F
with `AmpBound 2 K (A − b) η`; by P-linear, err_A(t) = err_b(t) + t^{2/3} I(A − b) − c_C (A − b)(0); the middle term is at
most C η by P-radius (bound), the last at most |c_C| η (order 0 at κ = 0), so ‖err_A(t)‖ < ε/2 + (C + |c_C|) η ≤ ε.

**S4.2O from S4.2U and P-mod.** Fix φ, take δ from S4.2U, A with a budget, R and ε. The modulation family is
C²-totally bounded (P-mod), so S4.2U gives T with the uniform estimate over the family; for ‖y‖ ≤ R,
`oscInt2 (fun κ => t φ κ + lin y κ) A = oscInt2 (fun κ => t φ κ) (e^{i lin y} A)` (`Complex.exp_add`, pointwise) and
`(e^{i lin y} A)(0) = A(0)` (`lin y 0 = 0`).

## Interface checks (numerical, before proofs)

`numerics/review/d4u_interface_checks.py`: (i) the ε/2 bookkeeping (η = ε / (2 (C + |c_C| + 1))); (ii) the modulation net: for a bump A and R = 2, the C² sup of the difference
`(e_y − e_{y′}) A` against ‖y − y′‖ on a grid, to confirm the Lipschitz-type behaviour the compactness argument
relies on (the argument itself does not need the constant); (iii) the identity absorbing the offset into the
amplitude and its value at 0. Run 2026-11-15 (python 3.13.18, numpy 2.5.3): RESULT PASS; the ratio C²-size of the
difference over ‖y − y′‖ stays about 11–12 as ‖y − y′‖ goes from 1e−1 to 1e−4; the identity holds to 2.5e−14.

## Effort

P-radius and P-linear: tens of lines each. P-mod: the bulk (the complex slice lemma, joint smoothness, uniform
continuity, the net), estimated 150–300 lines. Assembly: about 80 lines.

## Revision after the route referee

One fresh-context route referee (a Claude instance, like the lead; prompt and report not recorded, lessons 46) read the
route, the blueprint and the compiled assembly at 378d5ae, launched 13:50:47 UTC, run time 245.6 s; it ran small Lean
probes of names and definitions in its own scratch directory and wrote no proof of a part; nothing was committed while
it read. Verdict: SOUND, no BLOCKER or MAJOR; the findings, in the lead's words, and the answers:
1. MINOR. In P-mod, `fun_prop` does not handle the coercion ℝ → ℂ: use `Complex.ofRealCLM.contDiff.comp` for it,
   `unfold lin` before `fun_prop` for the real part, `Complex.contDiff_exp` and `.mul` for the rest. Accepted (brief).
2. MINOR. The slice derivatives for j = 0, 1, 2 have different types, so take one ρ per order and their minimum (or an
   eventually-statement over `Finset.range 3`). Accepted (brief).
3. NIT. The complex-valued slice identity: the proof of `OscInt.API.FamilyAux.iteratedFDeriv_slice` goes through for a
   general normed codomain; put the general version as a local lemma in the D4U proof file, not as an edit of
   `OscInt/Front/FamilyC10.lean`. Accepted.
4. NIT. Each member's budget can come from `OscInt.API.ampBoundOfContDiff` directly. Accepted.
5. NIT. "The assembly" says T = max T₀ 1; the Lean intersects with `eventually_ge_atTop 1`, which is the same. Wording
   noted here; no change.
The referee checked that every name the route cites exists at the pin, that both assembly theorems have exactly the
frozen statement types and depend on the standard axioms only, and estimated P-radius at 30–50 lines, P-linear at
15–30 and P-mod at 120–220, with mechanical risk only. Lead's note for P-linear: `HasCompactSupport.mul_left` with a
lambda target times out at the pin (unification of `f * f'` with the pointwise lambda); derive compact support from
`tsupport_mul_subset_right` and `IsCompact.of_isClosed_subset` instead.
