# Proof route for batch A3: S5.1′ and S5.1 (uniform cusp bound t^{−3/4})

Statements: `CuspBoundGenStatement` (S5.1′) and `CuspBoundStatement` (S5.1) in `OscInt/Statements/Cusp.lean`, frozen
2026-11-09 (stamp `stamps/20261109T201548Z-fcb46d9a6239`) and reviewed before any proof. S1.k (`VdCkStatement`) is
not part of this route. It is anticipated by Roos–Praveen (`docs/prior_art.md`) and will be ported separately.

The mathematics is the hand proof re-derived in `review/2026-11-10-external-results-answers.md` (an AI-assisted
route, disclosed in `docs/prior_art.md`). It was checked by the lead and by a fresh-context referee, and its algebra is
checked by `numerics/review/cusp_proof_checks.py` (7/7). This document maps it onto OscInt's existing machinery.

**Blueprint:** `Blueprint/Cusp.lean`, one `…Facts` proposition per part.

**Assembly:** `OscInt/Cusp/Assembly.lean`, by the lead, compiled before any part is proved.
- `cuspBoundGen_of (hCE : CoreEstimate4Facts) (hND : NormalizedData4Facts) (hNS : TransverseNonStatFacts)
  (hN : A3NormalizeFacts) : CuspBoundGenStatement`.
- `cuspBound_of_gen : CuspBoundGenStatement → CuspBoundStatement` (a stable A3 point is an A3 point).
- Both depend only on `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`, 2026-11-10).

## Why this route

S2/S3's core estimate L6 (`OscInt/StationaryPhase/Core.lean`) already proves the transverse dephasing.
- `core_reduction` writes the 2D integral as the 1D integral `∫ e^{im g(x)} F(x) dx`, with `g(x) = Q(x, ys x)` and
  `F(x) = ∫ e^{im(Q(x,t) − g(x))} A(x,t) dt`.
- It shows `ampNorm F F' ≲ M (mμ)^{−1/2}` using only `AmpBound 2`.
- The outer step is then S1.2 (j = 2) or S1.3 (j = 3).

The cusp is the case j = 4. It needs three things the core does not yet have:
1. an order-4 outer van der Corput estimate (P1);
2. an outer linear term `p x` with `p` unbounded (P2): the frozen statements are uniform in every `y ∈ ℝ²`;
3. normalized data built from the *reduced* quartic, not the raw one (P3).

Large transverse frequencies are handled by one integration by parts (P4). The A3 hypothesis is turned into
coordinates by P5.

Not needed: the parametrised transverse lemma I3a, S1.k, the dyadic rescaling of S4, and the stability conjunct
(`T ≠ 0`).

## The parts

### A3-P1 `VdC4Facts`: order-4 van der Corput, constant 38, from S1.3

S1.k at k = 4 (`5·2³ − 2 = 38`), uniform in a linear term, with `DerivChain` hypotheses. Proof: one level up from
`OscInt.VanDerCorput.HigherAux.vdc3Plain`.
1. **Split.** `SplitFacts` (`splitFacts`) applied to `D 3`, whose derivative `D 4` satisfies `|D 4| ≥ μ` on (a,b). This
   gives a monotone `D 3` and a point `d` with `μ|x − d| ≤ |D 3 x|`. The Darboux step is inside `splitFacts`
   (`hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne`, checked).
2. **Cut.** Cut at `d ∓ r` with `r = μ^{−1/4}`. The middle piece is ≤ 2r. On the outer pieces `|D 3| ≥ μr = μ^{3/4}`,
   and `VdC3PlainFacts` gives `18 (μ^{3/4})^{−1/3} = 18 μ^{−1/4}` on each. Total: 38 μ^{−1/4}.
3. **Amplitude.** `amplitudeTransfer` (`AmplitudeTransferFacts`) adds the amplitude.
4. **Linear term.** The linear term `p x` changes only `D 1` (to `D 1 + p`), as in S1.3's final assembly
   (`OscInt/VanDerCorput/Final.lean`).

Interface check: P4 of `numerics/review/cusp_proof_checks.py` (`2η/λ + 36η^{−1/3} = 38λ^{−1/4}` at `η = λ^{3/4}`).

### A3-P2 `CoreEstimate4Facts`: core estimate of order 4 with an outer linear term

Under `CoreHyps 4 a b μ ν D Q ys`, `‖oscInt2 (m(Q + p x)) A‖ ≤ C M m^{−3/4}`, with `C = C(a,b,μ,ν,D)` uniform in
`p ∈ ℝ`.
1. **Outer linear term.** `Q' = Q + p x` has the same critical curve (`∂_yQ' = ∂_yQ`). Its inner integral is
   unchanged, because `Q'(x,t) − Q'(x, ys x) = Q(x,t) − Q(x, ys x)`. The outer phase becomes `m g(x) + (mp) x`. So
   `oscInt2_eq_iterated` (applied with `γ = clamp a ys`) and `amplitude_facts` give the same F and the same
   `ampNorm` bound. The linear term enters only the outer oscillatory integral, where P1 is uniform in it. **Do not
   put `p x` into `Q`:** `CoreHyps` bounds `‖iteratedFDeriv i Q‖` for every `i ≤ 4`, including `i = 1`, so an
   unbounded `p` would break D.
2. **Phase chain to order 4.** Extend `phase_facts` from three to four derivatives of `m g`. This needs only
   `ys ∈ C³`, which `CoreHyps` provides. By `hasDerivAt_reduced`, `g′ = ∂_xQ(x, ys x)` (using `∂_yQ(x, ys x) = 0`), and
   `∂_xQ ∈ C³` because `Q ∈ C⁴`. So `g ∈ C⁴` on the open interval, and `hasDerivAt_iteratedDeriv_of_contDiffOn` gives
   the chain up to `iteratedDeriv 4`. Do not try to get `g ∈ C⁴` from `Q ∘ (id, ys)` with `ys ∈ C⁴`: `CoreHyps` does
   not give `ys ∈ C⁴`.
3. **Outer step.** P1 with `μ := mν` and linear coefficient `mp`. Then
   `38 (mν)^{−1/4} · 8 (mμ)^{−1/2} · Y = 304 ν^{−1/4} μ^{−1/2} Y m^{−3/4}`, where
   `Y = (1 + 4b)(1 + 2a(1 + 24β⁶)) M` as in `coreEstimate`. Write the arithmetic as `arith4`, after `arith3`.

### A3-P3 `NormalizedData4Facts`: uniform data from a normal point of order 4

`NormalPoint4 Ψ` (`Blueprint/Cusp.lean`) is defined as follows:
- `∂_yΨ(0) = 0`, `∂²_yΨ(0) ≠ 0` and `∂_x∂_yΨ(0) = 0`;
- the *reduced* quartic is nonzero: `∂⁴_xΨ(0) − 3(∂²_x∂_yΨ(0))²/∂²_yΨ(0) ≠ 0`. The raw quartic would be wrong: the
  bite `(y + x²/2)²` in `OscInt/Front/CuspSanity.lean` has raw quartic 6 and reduced quartic 0.

Proof by `ImplicitAux.exists_coreHyps 4 G4`, which is generic in `j` and the formula `G`. Three facts are new:
1. **The formula.** Define `G4 Q k := fderiv ℝ (G3 Q) k (1, Y1 Q k)`, the derivative of `G3` along the curve's tangent.
   Prove `SliceHyps.iteratedDeriv_four_reduced`, i.e. `iteratedDeriv 4 g x = G4 Q (x, ys x)` on `Ioo (−2a) (2a)`.
   Use `iteratedDeriv_three_reduced` (`g‴ = G3 Q (x, ys x)`), the chain rule along the graph
   (`hasDerivAt_comp_graph`, `SliceHyps.hasDerivAt`), and `ys′ = Y1`.
2. **Continuity.** `(τ, k) ↦ G4 (Q τ) k` is continuous at `(τ₀, 0)`. `G3` involves third derivatives and `Y2`; its
   derivative involves fourth derivatives of `Q`, which `FamilyCk 4` makes jointly continuous. Follow
   `continuousAt_G3`. This is the heaviest new piece.
3. **Value.** `G4 (Q τ₀) 0` equals the reduced quartic of `NormalPoint4`. At 0, `Y1 = 0` (from `∂_x∂_y = 0`) and
   `Y2 = −∂²_x∂_y/∂²_y`, so `G4 = ∂⁴_x + 3 ∂²_x∂_y · Y2 = ∂⁴_x − 3(∂²_x∂_y)²/∂²_y`. This is the seven-term chain rule at
   `c′ = 0`, `c″ = −T/h₀` (checks P1 and P2 of `cusp_proof_checks.py`). The fourth derivative in `NormalPoint4` is
   written with `iteratedFDeriv ℝ 4`; connect it to the derivative of `ddd` by `iteratedFDeriv_succ_apply_left`
   (checked), as `ddd_eq_iteratedFDeriv` does at order 3 (argument order reversed: `ddd f k u v w =
   iteratedFDeriv ℝ 3 f k ![w, v, u]`).

### A3-P4 `TransverseNonStatFacts`: large transverse frequency

If `|∂_yΦ| ≥ c` and `|∂²_yΦ| ≤ D` on the box, then `‖oscInt2 (mΦ) A‖ ≤ C M / m` for A supported in the box, with
`C = C(a,b,c,D)`. Nothing is assumed in x, so a linear term with any p is allowed.
- **Proof.** Fubini (`oscInt2_eq_iterated` with `γ = 0`, or `MeasureTheory.integral_prod`), then one integration by
  parts in y on each slice (`CoreAux.ibp_phase` with `q = ∂_yΦ`, weight `A/(m ∂_yΦ)`).
- **Boundary terms.** They vanish: A is continuous and zero outside the closed box, hence zero on its boundary.
- **Bound.** `|∂_y(A/∂_yΦ)| ≤ M/c + M D/c²` (an `AmpBound 1` amplitude). Integrating over the box gives
  `C = 4ab(1/c + D/c²)`.

### A3-P5 `A3NormalizeFacts`: from `IsA3Point` to `NormalPoint4`

Given the frozen witnesses `v, w`, take `L(u, s) = u v + s w` and `F = φ ∘ L − φ(0) − Dφ(0) ∘ L`.
1. **`L` is invertible.** First, `v ≠ 0`, since the A3 invariant is multilinear in `v` and would vanish. Second,
   `D²φ(0)[v, ·] = 0` while `D²φ(0)[w, w] ≠ 0`, so `w ∉ span{v}`. Hence `det L ≠ 0`
   (`LinearMap.equivOfDetNeZero`, then `LinearEquiv.toContinuousLinearEquiv`, both checked).
2. **Derivatives of F.** By `ContinuousLinearMap.iteratedFDeriv_comp_right` (checked), the derivatives of `F` at 0
   are those of φ applied to `L e₁ = v` and `L e₂ = w`:
   - `∂_yF(0) = Dφ(0)[w] − Dφ(0)[w] = 0`;
   - `∂²_yF(0) = D²φ[w,w] ≠ 0`;
   - `∂_x∂_yF(0) = D²φ[w,v] = 0` (symmetry, `dd_comm`, and the kernel condition);
   - `∂⁴_xF(0) = D⁴φ[v⁴]` and `∂²_x∂_yF(0) = D³φ[v,v,w]`.
3. **The reduced quartic.** The reduced quartic of `NormalPoint4` is `(h₀ Q − 3T²)/h₀ ≠ 0`. Connect `dd`/`ddd` to
   `iteratedFDeriv` with `dd_eq_iteratedFDeriv` and `ddd_eq_iteratedFDeriv` (mind the argument order).

## The assembly (`OscInt/Cusp/Assembly.lean`, compiled)

1. **Normalise.** P5 gives L. The family `Q q = F + lin (0, q)` is `FamilyCk 4` (`familyAddLinear` with
   `sanity_familyCk_const`, and `familyCk_comp`). It has `NormalPoint4 (Q 0)`.
2. **Uniform data.** P3 gives `CoreHyps 4` for `q` in a neighbourhood U of 0. Choose a ball `(−ε, ε) ⊆ U` and set
   `q₀ = ε/2`.
3. **Far-case constants.** By continuity, `|∂_yF| ≤ q₀/2` on a box `[−r, r]²`, and `|∂²_yF| ≤ D′` there (compactness).
4. **Radius.** `δ = min(a, b, r)/(‖L⁻¹‖ + 1)`. By `LocalCritAux.preimage_ball_subset_box`, `L⁻¹(closedBall 0 δ)` lies
   in both boxes.
5. **Change of variables.** For given A, M, y, t, `affineChange` and `ampBoundAffine` give `|det L|` and the amplitude
   bound `max(1, ‖L‖)² M`. The phase becomes `tφ(0) + t(F + q y + p x)`, with `p = Dφ(0)[v] + (y·v)/t` and
   `q = Dφ(0)[w] + (y·w)/t` (`AssemblyAux.phase_eq`). The constant drops out (`norm_oscInt2_const_add`).
6. **Two cases.**
   - `|q| ≤ q₀`: P2 with the CoreHyps of `Q q`.
   - `|q| > q₀`: P4 for `Φ = F + lin (p, q)`, since `|∂_yΦ| ≥ |q| − q₀/2 ≥ q₀/2`; then `t^{−1} ≤ t^{−3/4}`.
7. **Constant.** `C = |det L| · max(C₂⁺, C₄⁺) · max(1, ‖L‖)²`.

## Order of work and dependencies

P1 must come before P2. P3, P4 and P5 are independent of each other and of P1/P2. The final file
`OscInt/Cusp/Final.lean` will contain:
- `theorem OscInt.cuspBoundGen : CuspBoundGenStatement := cuspBoundGen_of coreEstimate4 normalizedData4
  transverseNonStat a3Normalize`;
- `cuspBound` by `cuspBound_of_gen`;
- then the `#assert_type_is` lines, `OscInt.API.cuspBound(Gen)` for the comparator, the replay and post-proof review
  (CONTRIBUTING steps 7–10).

## Risks known now

- **P3, continuity of `G4`.** Defining `G4` as a directional derivative keeps the formula short. But continuity then
  needs `G3 ∘ Q τ` to be C¹ jointly in `(τ, k)`. If that is heavy, write `G4` explicitly from the seven-term formula,
  with `Y3 = ys‴`, which needs fourth derivatives of `Q`.
- **P2, outer linear term.** If `oscInt2_eq_iterated` resists the rewriting, prove the linear-term version of
  `core_reduction` directly. The inner integral `innerF` is literally unchanged.
- **Amplitude regularity.** Everything uses `AmpBound 2` or `AmpBound 1`, as the frozen statements require.
  Nothing needs C³.
