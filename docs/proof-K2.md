<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch K2: proof route

Written by the lead on 2026-11-28, after the answers to the blind pre-proof reviews were stamped
(`stamps/20261128T023440Z-e368c37563ab`). The statements are `OscInt/Statements/TriangularDecay.lean`; the prose is
`docs/statements.md`, "Batch K2". The route follows the decision record (section 7 of
`review/2026-11-28-K2-packet-answers.md`), which rests on an external research packet and on route referee J's
findings (section 6 there). The blueprint is Blueprint/TriangularDecay.lean (committed after the route referee): one proposition per part, proved as
`theorem OscInt.K2.<part>`. The assemblies are the lead's. Every part is uniform as stated; no part may weaken its
proposition, and an agent that finds a part false stops and reports.

Notation as in the statement file. `F(u, s) = Ψ(k₀ + uv + sw) − Ψ(k₀) − DΨ(k₀)(uv + sw)` is the chart phase; `Q_q = F +
q·s` is the family with transverse velocity q; `ys q` is its critical curve; `g_q(x) = Q_q(x, ys q x)`.

## 1. K2-L, the local bound of order m (parts P1, P2, P3; P4 is proved)

Assembly: a clone of `OscInt.Cusp.cuspBoundGen_of` (`OscInt/Cusp/Assembly.lean`) with the order 4 replaced by m. In
coordinates `κ = k₀ + L k`, `L(u, s) = uv + sw` (P3), the affine change (`affineChange`, the same lemma as there)
turns `∫ e^{i(tΨ + y·κ)} A` into `|det L| e^{it·const} ∫ e^{it(Q_q + p u)} A∘(k₀ + L·)` with p, q real (Assembly's
`phase_eq`). For `|q| ≤ q₀` use P1 with the data of P2; for `|q| > q₀` use `OscInt.Cusp.transverseNonStat` (P4) on a box
where `|∂_s F| ≤ q₀/2`, which gives `t^{−1} ≤ t^{−(1/2 + 1/m)}` since `m ≥ 2`.

**P1 `CoreEstimateMFacts`.** A clone of `OscInt.Cusp.coreEstimate4` (`OscInt/Cusp/Core4.lean`):
- amplitude: `OscInt.StationaryPhase.CoreAux.amplitude_facts`, unchanged;
- outer integral: `OscInt.Cusp.Core4Aux.oscInt2_eq_outer_linear`, unchanged;
- derivative chain: `D 0 = t·Q(x, clamp a ys x)`, `D j = t · iteratedDeriv j g` for `1 ≤ j ≤ m`. For j = 0 use
  `phase_facts`. For j ≥ 1 use `CoreAux.hasDerivAt_iteratedDeriv_of_contDiffOn`, with g smooth on `(−2a, 2a)`
  because Q is smooth and `ys` is `C^∞` there;
- van der Corput: `OscInt.API.vdCk` of order m, lower bound `tν`, linear term `tp`;
- exponents: `Core4.arith4` with 4 replaced by m, giving
  `C = 8 c_m ν^{−1/m} μ^{−1/2} (1 + 4b)(1 + 2a(1 + 24 β₀⁶))`, `c_m = 5·2^{m−1} − 2`.

**P2 `NormalizedDataMFacts`.** Referee J's repair J-1. The repository's uniformity lemma
`OscInt.StationaryPhase.ImplicitAux.exists_coreHyps` (`Implicit.lean`, line 507) is generic in the order j. It takes
a formula `G` with `iteratedDeriv j (reduced) = G (Q τ) (x, ys x)` and continuity of `G (Q τ) k` at `(τ₀, 0)`.

With `Y1 = −Q_xy/Q_yy` and `D f = f_x + Y1 f_y`:
- `d/dx f(x, ys x) = (D f)(x, ys x)`, because `ys′ = Y1(x, ys x)`;
- hence `iteratedDeriv j g = (D^{j−1} Q_x)(·, ys ·)` for j ≥ 1, by induction;
- so take `G := D^{m−1} Q_x`. It is a polynomial in partial derivatives of Q divided by powers of `Q_yy`, so it is
  continuous jointly in `(q, k)` where `Q_yy ≠ 0`.

New: generalise `SliceHyps.contDiffAt` from C³ to `C^n` for every n. The Mathlib theorem
`ContDiffAt.contDiffAt_implicitFunction` takes any n. Then `CoreHypsM` replaces `CoreHyps` (smooth root).

Two alternatives:
- a joint implicit function theorem in `(q, u)`;
- for m = 6 only, the explicit A5 root `h = arcsin((sin θ + q/2)/cos u) − θ` of referee J.

Either may be used if the operator route stalls; a part's proposition does not change.

**P3 `ChartFacts`.** Algebra:
- `F(u, h u) = reducedFn Ψ k₀ v w h u − Ψ k₀`, so the m-th derivatives agree for m ≥ 1;
- `∂_s F(u, s) = DΨ(k₀ + uv + sw) w − DΨ(k₀) w`, which is 0 on the curve by `ReducedCurve`;
- `∂²_s F(0) = D²Ψ(k₀)[w, w] ≠ 0`;
- L is invertible by the spanning hypothesis.

The derivative forms are those of TRI's sanity and proof modules (`OscInt.API.dd_iteratedFDeriv`).

## 2. K2-U, the global upper bound (parts P5, P6, P7; lead's assembly)

- **α = 0.** `OscInt.API.latticeLaplacianCubeRoot` (T6E′) with `triKernel 0 = latticeKernel` (sanity layer
  `triKernel_zero`).
- **α ≠ 0.** At each `k₀ ∈ ℝ²` TRI-K gives one of three cases. In each a local bound of order `≥ triRate α` holds,
  uniform in the linear term:
  - **A1/A2 (`FoldOrNondeg`).**
    - Nondegenerate point: choose w with `D²Ψ[w, w] ≠ 0` (polarisation) and v independent; P5 gives a reduced
      curve; P6 gives `g″(0) = det/D²Ψ[w, w] ≠ 0` (Schur complement); K2-L with m = 2.
    - Fold: kernel v, transverse w; P5; `ReducedBridge.bridge` gives `g‴(0) = D³Ψ[v³] ≠ 0`; K2-L with m = 3.
  - **A3 (`IsA3Point`).** `OscInt.API.cuspBoundGen` (S5.1′) translated to k₀, or P5 plus the bridge plus K2-L with
    m = 4.
  - **A5 (`IsA5Point`; only at `|α| = a*`, by TRI-X).** Its own v, w, ε and h; K2-L with m = 6.

  Exponents: 1, 5/6, 3/4, 2/3. Each is at least `triRate α`, using TRI-X to exclude A5 when `|α| ≠ a*`.
- **P7 `TorusPatchFacts`.**
  - T1 (`OscInt.API.torusUnfold`) gives `∫_{box} g = ∫ η g` for the continuous biperiodic integrand.
  - Cover the compact `tsupport η` by finitely many balls from the local bounds.
  - Take the telescoping partition `χ_j = b_j ∏_{i<j}(1 − b_i)`, with `b_j` smooth bumps equal to 1 on smaller balls
    that still cover.
  - `ampBoundOfContDiff` (F1) bounds each `η χ_j`. Sum.
  - `t ≥ 1` turns each local exponent into `triRate α` (`Real.rpow_le_rpow_of_exponent_le`).
- **P5 `ReducedCurveExistsFacts`.** The implicit function theorem for `s ↦ DΨ(k₀ + uv + sw) w − DΨ(k₀) w` at
  `(0, 0)`, then a smooth global extension by a cutoff, the pattern of `TriWitness.exists_curve`.
- **P6 `ReducedOrderTwoFacts`.** Differentiate `g′ = DΨ(γ) v − DΨ(k₀) v` once more and use `h′(0) = −D²[v, w]/D²[w, w]`
  from the curve equation.

## 3. K2-MA and K2-ML (parts P10a, P10b; K2-ML is the lead's corollary)

**P10a `MonomialPositivityFacts`.** L1 of the packet, re-derived by the lead and by referee J:
1. On `[0, R]` substitute `y = x^m`. The singularity at 0 is handled on `[r, R]` with `r → 0`.
2. `Re ∫_0^R cos(x^m) dx = ν ∫_0^{R^m} cos y · y^{ν−1} dy`, with `ν = 1/m`.
3. Integrate by parts: `= ν [sin Y · Y^{ν−1} + (1 − ν) ∫_0^{Y} sin y · y^{ν−2} dy]`.
4. The last integrand is integrable on `(0, ∞)`. The pattern is `D4/CosMoment.lean` with the exponent `−4/3`
   replaced by `ν − 2`.
5. Its integral is at least the first half-period pair, by the pairing of `CosMoment.integral_period_pos`.
6. That pair is at least `∫_{1/2}^{1} (1/4)(2/3) = 1/12`, so the real part of each half-line limit is at least
   `ν/24`, and the total at least `1/(12m)`.

The real part does not depend on σ or on the parity of m, since `cos(σ x^m)` is even in x. The imaginary part
converges by one integration by parts on `[1, R]`. The limit along `R → ∞` of `∫_{−R}^{R}` is the sum of the two
half-line limits.

**P10b `MonomialTailFacts`.** L2:
- `I_b(t) − t^{−1/m} C = lim_R ∫_{−R}^{R} (b − 1) e^{itσx^m}`, after scaling `x ↦ t^{−1/m} x` in the improper integral;
- on `[r, R]` integrate by parts against `e^{itσx^m}`, with `d/dx = itσ m x^{m−1}`;
- the boundary at r vanishes (`b(r) = 1`), and the one at R tends to 0;
- `∫_r^∞ |b′| x^{1−m} ≤ r^{1−m}`, because b is monotone from 1 to 0, and `(m − 1)∫_r^∞ x^{−m} = r^{1−m}`;
- each side gives `2 r^{1−m}/(m t)`.

**K2-ML** from K2-MA: `|I_b| ≥ Re C · t^{−1/m} − 4/(m t r^{m−1}) ≥ t^{−1/m}/(24m)` exactly at the threshold.

## 4. K2-F, Fourier localisation (part P13; the lead's assembly)

Put `tp = n + δ` with `n = ⌊tp⌋` componentwise, so `δ ∈ [0, 1)²`. Then
`∫_{box} χ e^{it(Ψ + p·k)} = ∫_{box} (χ e^{iδ·k}) e^{i(tΨ + n·k)}`. The function `a = χ e^{iδ·k}` is smooth and
vanishes near the boundary of the box, so it is smooth on the torus.

Parseval on `UnitAddTorus (Fin 2)` (`hasSum_prod_mFourierCoeff`, `Mathlib/Analysis/Fourier/AddCircleMulti.lean`,
line 293), after rescaling the period 2π to 1, gives
`∫ a ḡ = Σ_j â_j conj ĝ_j`. Here `g = conj e^{i(tΨ+n·k)}` has coefficients `K(t, n + j)` up to normalisation. Hence
`|L| ≤ (2π)^{−2} (Σ_j |â_j|) sup_j |K(t, n + j)| ≤ D B`.

**P13 `FourierDecayFacts`.** Integrate by parts twice in each variable; there are no boundary terms, since a vanishes
near the boundary. This gives `|â_j| ≤ c / ((1 + j₁²)(1 + j₂²))` with c bounded by `∂₁ᵃ∂₂ᵇ a` for a, b ≤ 2, uniformly
in `δ ∈ [0, 1]²` (Leibniz). Summable, since `Σ 1/(1 + k²) = π coth π < 4`.

## 5. K2-D, the global lower bound (parts P9, P11, P12; the lead's assembly)

At each α, fix a witness:
- **α ≠ 0, `|α| ≠ a*`.** `(π/2, π/2)` with v = (1, −1), w = (1, 1) (TRI-Q):
  - P5 gives a reduced curve;
  - g′ = g″ = 0 by the curve and the kernel;
  - the bridge gives g‴ = 0 and `g⁗(0) = −12/(4α) = −3/α ≠ 0`, with `D²[w, w] = 4α` from `TriDeriv.triD2_mixed`;
  - m = 4.
- **`|α| = a*`.** The A5 witness of TRI-W (existential v, w, ε, h; derivatives 1–5 zero, 6 nonzero): m = 6.
  Referee J, J-6: use only the existential witness.
- **α = 0.** P12 at `(π/2, π/2)`.

Then:
1. P11 gives a smooth χ supported in a small ball around the witness, inside `(−π, π)²`. The localised integral at
   the velocity `p₀ = −∇Ψ(k₀)` equals `J⁻¹ e^{itc} I_{b₁,m,σ}(t) I_{b₂,2,ε}(t)`.
2. K2-ML for both factors gives `|L(t)| ≥ c₀ t^{−1/2−1/m}` for `t ≥ T₀`.
3. K2-F with that χ gives D. If every site had `|K(t, n)| < (c₀/D) t^{−β}`, then `|L(t)| < c₀ t^{−β}`, which is a
   contradiction.
4. So some site has `|K(t, n)| ≥ (c₀/D) t^{−β}`; shrink c to make the bound non-strict.

**P9 `ParamIntegralSmoothFacts`.** By induction on n, via `contDiff_succ_iff_fderiv`. The derivative of
`x ↦ ∫_0^1 f(x, τ) dτ` is `∫_0^1 ∂_x f(x, τ) dτ`, by `hasFDerivAt_integral_of_dominated_of_fderiv_le` on a compact
neighbourhood. For n = ∞, use every finite n. Mathlib has no `ContDiff` corollary at this pin (lead's check, section
5.2 of the packet answers).

**P11 `ProductNormalFormFacts`.** The lead's triangular substitution, validated by referee J (question 5).
1. **Root.** With the transverse root S(u) (the given reduced curve h, on `|u| < ε₀`), Taylor at S gives
   `F(u, s) − G(u) = (s − S(u))² R(u, s)`, with `R = ∫_0^1 (1 − θ) F_ss(u, S + θ(s − S)) dθ` smooth (P9) and
   `R(0, 0) = F_ss(0)/2 ≠ 0`.
2. **Transverse coordinate.** `w(u, s) = (s − S(u)) √|R(u, s)|` is smooth near 0, with `∂_s w(0, 0) > 0`, and
   `F = G + ε w²` with `ε = sign R(0, 0)`.
3. **Longitudinal coordinate.** `G(u) − G(0) = u^m R_m(u)`, with `R_m = ∫_0^1 (1 − θ)^{m−1}/(m − 1)! G⁽ᵐ⁾(θu) dθ`
   smooth (P9) and `R_m(0) ≠ 0`. Put `z(u) = u |R_m(u)|^{1/m}`, which is smooth with `z′(0) > 0`, and
   `σ = sign R_m(0)`.
4. **Cutoff.** `χ̃(u, s) = J⁻¹ b₁(z(u)) z′(u) b₂(w(u, s)) ∂_s w(u, s)`, with plateau cutoffs b₁, b₂ supported so small
   that `χ̃` vanishes near the chart's edges.
5. **The identity.** Fubini, then `intervalIntegral.integral_comp_mul_deriv` in s for each u, then in u, give the
   product exactly.

**P12 `SquareNormalFormFacts`.** At `(π/2, π/2)` the tangent-subtracted phase of `triPhase 0` is
`(a − sin a) + (b − sin b)` in `k = (π/2 + a, π/2 + b)`. Put `z(a) = a · (6 (a − sin a)/a³)^{1/3}/6^{1/3}`, which is
smooth with a smooth positive ratio (P9). Then `z³ = a − sin a`, and the product cutoff `b(z(a)) z′(a) b(z(b)) z′(b)`
makes the integral the square of `∫ b e^{itz³}`.

## 6. Order of work and checks

1. The lead commits the blueprint and the assemblies against it: K2-L from P1–P4, K2-U from P5–P7, K2-ML from
   K2-MA, K2-MA from P10, K2-F from P13, K2-D from P9, P11, P12, K2-F, K2-ML.
2. Agents prove P1, P2, P5/P6, P7, P9, P10, P11, P12 and P13 in parallel. Each agent runs one Lean process at a time
   (`nice -n 10`), writes only in its scratch directory, and works to a committed brief.
3. The lead verifies every returned part: build, forbidden-token scan, `#print axioms`, per-module `leanchecker`.
4. Then the statement-type checks, the comparator against the stamped export, the post-proof reviews (fidelity,
   soundness, adversarial), the owed plants A1 and A2, and the full isolated replay.

## 7. Risks named before the work

- **P2.** The operator identity needs a C^{m−1} root on an open interval, uniformly in q.
- **P11.** The size of the analysis, and the smoothness of `|R|^{1/2}` and `|R_m|^{1/m}` where R and R_m have a fixed
  sign.
- **P13.** The rescaling to `UnitAddTorus`.

The fallbacks are those named in section 1 and in referee J's report (J-1, J-5, Q6).

## 8. Revision after the route referee (2026-11-28; `review/2026-11-28-K2-route-referee-answers.md`)

Sections 1 to 7 are left as written; this section supersedes them where they differ.

1. **P2 (finding M1).** `ImplicitAux.exists_coreHyps` is not used unchanged. Its `hG` must hold for every
   `SliceHyps` phase, which is only C⁴, and its output hides a C³ root. P2 is proved by either of two routes:
   - **(a), recommended by R.** The operator `D f = f_x + Y1 f_y` does not depend on q, so `G(F + q·y) = G(F)`.
     - State the operator identity `g⁽ʲ⁾ = (D^{j−1}Q_x)(·, y(·))` for any differentiable curve with
       `Q_y(x, y(x)) = 0` on an open interval where `Q_yy ≠ 0`. Then `g⁽ᵐ⁾(0) = G(F)(0, 0)` along h directly.
     - The lower bound ν near q = 0 comes from continuity of `G(F)` at 0 and of the roots in q.
     - Smoothness of the box roots comes from a C^∞ version of `SliceHyps.contDiffAt`/`contDiffOn`, by the same
       uniqueness argument with n = ∞.
   - **(b).** A clone `exists_coreHypsM` with `ContDiff ℝ ∞` in its hypotheses, outputting `CoreHypsM`.

   The C^∞ slice lemma is shared with P5: P2 and P5 go to one agent.
2. **K2-F (finding M2).** New part P14 `TorusExpansionFacts`: the expansion of `χ e^{iδ·k}` integrated against any
   continuous g on the box. Route: pointwise inversion on the torus
   (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`) after rescaling, then `integral_tsum`. Only
   `χ e^{iδ·k}` is lifted to the torus. K2-F is then P13 + P14 with `g = e^{i(tΨ + n·k)}` and `D = S/(4π²)`. This
   replaces the Parseval sketch of section 4.
3. **P11 (finding M3).** The cutoff of section 5, step 4, is neither localised nor globally smooth as written.
   Repair:
   - define z and w with smooth substitutes for `√·` and `(·)^{1/m}`, valid on the range where R and R_m keep their
     sign;
   - multiply by a spatial plateau cutoff ζ, equal to 1 on a box where `z` and `w(u, ·)` are increasing, containing
     every point of a slightly larger box with `|z| < ρ₁` and `|w| < ρ₂`;
   - choose ρ₁, ρ₂ against that box;
   - for the complex integrand, use `intervalIntegral.integral_deriv_smul_comp`, not `integral_comp_mul_deriv`,
     which is real-valued.
4. **Small items:**
   - (m1) P5 needs the C^∞ slice lemma of item 1, not a pointwise `ContDiffAt`.
   - (m2) P3 is a part too.
   - (m3) P11 and P12 take P9 as a hypothesis.
   - (m5) At `(π/2, π/2)`: g′(0) = 0 by `ReducedBridge.hasDerivAt_reducedFn`; g″(0) = 0 by P6 and the kernel; at the
     A5 point the spanning hypothesis comes from the sanity layer's `span_of_hyps`.
   - (m6) At a nondegenerate point, P6's value is `hessDet · (v₁w₂ − v₂w₁)² / D²[w, w]`, or v, w are chosen among
     e₁, e₂, e₁ + e₂.
   - (N1) The clone of `phase_eq` carries the constant `lin y k₀`, and `lin (0, q) k` becomes `q * k.2`; in K2-U take
     `max C 0` before comparing exponents.
   - (N2) The CosMoment pairing is `OscInt.D4.CosMomentAux.integral_period_pos`, a pattern at exponent −4/3 only.
   - (N3) P9's parameter is in ℝ × ℝ; the one-variable remainders compose with `u ↦ (u, 0)`.
   - (N4) P13 more cheaply: `c_j(δ)` is the transform of χ alone at `j − δ`, and `1 + (j − δ)² ≥ (1 + j²)/4` for
     δ ∈ [0, 1].
   - (N5) P11 and P12 share a one-variable monomial-coordinate lemma, which goes to one agent.
   - (N7) Part theorems are named in lowerCamel.
5. **Rule 12 (m4).** The Mathlib names of the route are in `MathlibNames.lean`. `CosMoment.integral_period_pos` is
   the repository name `OscInt.D4.CosMomentAux.integral_period_pos` (N2).

Agents: P1; P2 with P5 and P6; P3; P7; P9; P10a with P10b; P11 with P12; P13; P14.

## 9. As proved (2026-11-28; post-proof referees B and C)

Where the proofs differ from sections 1 to 8, as their module docstrings say:
- **P2.** Section 8, item 1, option (a). `Gop` is the operator, `Gop_addq` its q-independence, and the constants come
  from continuity at 0 of functions of k alone.
- **P7.** The repository's partition of unity `StationaryPhase.PartitionAux.exists_smooth_partition_compact` replaces
  the telescoping product. The exponent conversion to `triRate α` is in `TriDecayUpperAux.local_bound` (with
  `max C 0`).
- **P10a.** A direct lower bound replaces the substitution and the half-period pairing. With `a = 2^{1/m}`,
  `cos(x^m) ≥ 1 − x^{2m}/2` on `[0, a]` and a tail bound `a/m` give a real part of at least
  `a(1 − 2/(2m + 1) − 1/m) ≥ 1/(24m)` per half-line, since `a ≥ 1`. Convergence is by the Cauchy criterion.
- **P11.** No separate spatial plateau. The smooth substitutes for the roots are bounded below everywhere, so the
  cutoff's support already lies where the normal form holds. The 1D substitution `subst_line` needs `|φ(x)| ≥ c|x|`,
  not injectivity.
- **P12.** The same monomial-coordinate lemma, applied to `a − sin a` with m = 3.
- **P13.** Integration by parts on the whole plane (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
- **P14.** `hasSum_integral_of_summable_integral_norm` instead of `integral_tsum`.
- **K2-U, the A3 branch.** P5, the bridge and K2-L with m = 4, not S5.1′ (section 2 allowed either).
