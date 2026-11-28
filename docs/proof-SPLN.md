<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Proof route of batch SPL-N (SPL-NU, SPL-NL, SPL-NK, SPL-NC)

Written by the lead after the blind pre-proof reviews (answers `review/2026-11-28-SPLN-A5U-LOC2-preproof-answers.md`, stamped `stamps/20261128T154444Z-e9c0ea9fb732`). Mathematics only; every Mathlib name
below is checked at the pin with its full signature in `MathlibNames.lean` (lessons 1, 19) before any part is proved.
Source: the external packet of 2026-11-28 (`review/2026-11-28-postK2-packet-answers.md`, section 3, where the lead
re-derived each step). Notation: `E(v) = e^{iv²/2}` (`fresnelE` in `OscInt.StationaryLeadingAux`), `F = fresnelPrim`,
`L = fresnelLimit`, `κ₊ = splKernelPos`, `κ = splKernel`, `s = √π`.

## 1. Plan

| Part | Proposition (blueprint `Blueprint/StationaryLeadingSharp.lean`) | Content |
|---|---|---|
| N1 | `SplnFormulaFacts` | for `x ≥ 0`: `κ₊(x) = x + iLx²/2 − i Φ(x)`, `Φ(x) = ∫₀ˣ (x − v)² E(v)/2 dv` |
| N2 | `SplnTaylorFacts` | for `0 ≤ x ≤ 4`: `‖Φ(x) − Σ_{j<32} i^j I_j(x)‖ ≤ 2 I_32(x)`, `I_j(x) = x^{2j+3}/(2^j j! (2j+1)(2j+2)(2j+3))` |
| N3 | `SplnSqrtPiFacts` | `s₀ ≤ √π ≤ s₁`, `s₀ = 1772453850905516/10¹⁵`, `s₁ = s₀ + 10⁻¹⁵` |
| N4 | `SplnSecondFacts` | `κ₊` has derivative `κ₁ = E + ix(L − F)` and `κ₁` has derivative `i(L − F)` on `(0, ∞)`; `‖L − F(x)‖ ≤ 2/x` |
| N5 | `SplnInterpFacts` | vector interpolation: `f : ℝ → ℂ` with `f′`, `f″` on `[a, b]`, `‖f″‖ ≤ M` ⇒ `‖f(x)‖ ≤ max(‖f(a)‖, ‖f(b)‖) + M(b − a)²/8` |
| N6 | `SplnCellFacts` | generic cell soundness: the rational inequalities at both endpoints and both `s₀, s₁` ⇒ `‖κ₊‖ ≤ q` on `[a, b] ⊆ [1/2, 4]` |
| N7 | arithmetic | the 40 cells and the cover of `[1/2, 4]` by `decide`/`norm_num` over ℚ |
| N8 | `SplnBranchFacts` | `‖κ₊(x)‖ ≤ 11/16` on `[0, 1/2]`; `‖κ₊(x)‖ ≤ 277/400` on `[4, ∞)` |
| N9 | `SplnLowerFacts` | `72197399/10⁸ < ‖κ₊(8123/5000)‖` |
| A | assembly | SPL-NU from N6–N8 and oddness; SPL-NL from N9; SPL-NK from SPL-I and SPL-NU; SPL-NC from SPL-A, SPL-NL |

## 2. Mathematics per part

**N1.** Both sides vanish at 0 with derivative 1 there; their second derivatives on `(0, ∞)` are both `i(L − F)`
(left: two differentiations of the frozen formula, using `F′ = E`, `E′ = ixE`; right: expand
`(x − v)² = x² − 2xv + v²`, so `Φ = x²F/2 − xG₁ + G₂/2` with `Gₖ(x) = ∫₀ˣ vᵏE`, `Φ′ = xF − G₁`, `Φ″ = F`). Equal second
derivatives and equal 1-jets at 0 give equality on `[0, ∞)` (the difference is affine on `[0, ∞)` by two applications
of the mean value theorem with zero derivative; continuity at 0).

**N2.** `Φ(x) − Σ_{j<32} i^j I_j(x) = ∫₀ˣ (x − v)²/2 · (E(v) − Σ_{j<32} (iv²/2)^j/j!) dv` because
`∫₀ˣ (x − v)² v^{2j} dv = 2x^{2j+3}/((2j+1)(2j+2)(2j+3))`. By `Complex.exp_bound' : ‖x‖ / n.succ ≤ 1/2 → ‖exp x − Σ_{m<n} x^m/m!‖ ≤ ‖x‖^n/n! · 2` (checked at the pin) with
`n = 32` and `‖iv²/2‖ = v²/2 ≤ 8` (so `8/33 ≤ 1/2`) the bracket is at most `2 (v²/2)^{32}/32!`; integrating the positive weight
gives `2 I_32(x)`. The factor 2 costs nothing: the lead re-ran the packet's certificate with the remainder multiplied
by 2 and by 4 (all 40 cells pass; minimum squared slack `9.09·10⁻¹⁰`, set by the interpolation pad).

**N3.** `Real.pi_gt_d20 : 3.14159265358979323846 < π` and `Real.pi_lt_d20 : π < 3.14159265358979323847` (checked at
the pin, session 17); exact arithmetic gives `s₀² < 3.14159265358979323846` and `3.14159265358979323847 < s₁²` (lead's
check), so no Machin formula is needed; then `Real.sqrt_le_sqrt`, `Real.sqrt_le_left`, `Real.lt_sqrt`.

**N4.** Existing: `splKer_hasDerivAt_kernelPos`, `splValue_tendsto_prim` hypothesis form `‖F x − L‖ ≤ 2/x`
(`OscInt/Front/StationaryLeadingKernel.lean`, `StationaryLeadingFresnelValue.lean`, `SplFresnelFacts`); only the
derivative of `κ₁` is new.

**N5.** `g(x) = f(x) − ℓ(x)` with `ℓ` the chord. Either the Bochner/interval-integral representation
`g(x) = −[(b−x)/(b−a) ∫ₐˣ (s−a) f″ + (x−a)/(b−a) ∫ₓᵇ (b−s) f″]`, or (simpler in Lean) the scalar trick: for each
unit-norm functional `ℓ*` (or, in ℂ, `Re(conj(w) ·)` with `|w| = 1`) the real function `φ = Re(w̄ g)` has
`|φ″| ≤ M`, `φ(a) = φ(b) = 0`, hence `|φ(x)| ≤ M(x − a)(b − x)/2` by the classical real argument (compare with the
parabola `±M(x − a)(b − x)/2`, maximum principle via the mean value theorem); choosing `w = g(x)/‖g(x)‖` gives the
norm. No factor √2.

**N6.** On `[a, b] ⊆ [1/2, 4]`: `M = 2/a` (N4), so `‖κ₊(x)‖ ≤ max(‖κ₊(a)‖, ‖κ₊(b)‖) + (b − a)²/(4a)`. At an endpoint
`x`, by N1 and N2, `κ₊(x) = P(x, s) + e` with `‖e‖ ≤ 2 I_32(x)`, where `P(x, s) = (R(x) − s x²/4) + i(J(x) + s x²/4)`
and `R, J` rational polynomials (`L = s(1 + i)/2`, so `iLx²/2 = s x²(−1 + i)/4`). `P` is affine in `s`, so its norm is
convex in `s` and `‖P(x, √π)‖ ≤ max(‖P(x, s₀)‖, ‖P(x, s₁)‖)` by N3. The certificate checks
`budget = q − (b − a)²/(4a) − 2I_32(x) ≥ 0` and `‖P(x, sᵢ)‖² ≤ budget²`.

**N7.** Data: the 40 cells of the packet's `results/spl-cells.json` as a list of pairs of rationals. One
`decide`-style Boolean checker over ℚ, proved sound once (`checker = true → ∀ cells, inequalities`), and evaluated by
the kernel (`decide +kernel` was measured at 1.3 s for 40 cells in session 15; `native_decide` is forbidden).

**N8.** Small branch: `‖κ₊(x)‖ ≤ x + ‖L‖x²/2 + x³/6` by N1 (`‖E‖ = 1`, `∫₀ˣ (x − v)²/2 = x³/6`), `‖L‖ = √(π/2) ≤ 4/3`
(`π < 32/9`), at most `1/2 + 1/6 + 1/48 = 11/16` on `[0, 1/2]`. Tail: with `J₀ = L − F`, `J₂ = ∫ₓ^∞ E v^{−2}`,
`J₄ = ∫ₓ^∞ E v^{−4}` (improper integrals as limits of interval integrals; `J₄` and `J₂` absolutely convergent),
integration by parts gives `J₀ = iE/x − iJ₂`, `J₂ = iE/x³ − 3iJ₄`, hence
`κ₊ − L/2 = −E/(2x³) − (3i/2)(x² + i)J₄`. One more integration by parts, `J₄ = iE/x⁵ − 5iJ₆` with
`‖J₆‖ ≤ ∫ₓ^∞ v^{−6} = 1/(5x⁵)`, gives `‖J₄‖ ≤ 2/x⁵`. (The direct bound `‖J₄‖ ≤ 1/(3x³)` is NOT enough: it leaves a
term `≈ 1/(2x) = 1/8` at `x = 4`.) Hence `‖κ₊ − L/2‖ ≤ (1/2 + 3√(1 + x^{−4}))/x³ ≤ 4/x³` for `x ≥ 2`
(`√(17/16) ≤ 7/6`). With `‖L‖/2 ≤ 63/100` (`π < 22/7`) and `x ≥ 4`: `‖κ₊‖ ≤ 63/100 + 1/16 = 277/400`.

**N9.** At `x₀ = 8123/5000`, `s_m = (s₀ + s₁)/2`: `‖κ₊(x₀)‖ ≥ ‖P(x₀, s_m)‖ − 2I_32(x₀) − (s₁ − s₀)x₀²/4` (each coordinate of `P(x₀, √π) − P(x₀, s_m)` is at most
`(s₁ − s₀)x₀²/8`, and the norm is at most the sum of the two), and the exact squared comparison of the packet with
this error (the packet used `I_32`; the factor 2 is re-checked in the same run as N2's).

**Assembly.** SPL-NU: for `τ ≥ 0` split `[0, 1/2]`, `[1/2, 4]` (cover), `[4, ∞)`; for `τ < 0` oddness
(`splKer_kernel_neg`). SPL-NK: as `stationaryLeadingSevenEighths_of` with SPL-NU in place of the 7/8 kernel bound
(`splB_norm_remainder_le`). SPL-NC: given `c ≤ q_low` and the universal bound with `c`, take `ε = (‖κ(x₀)‖ − c)/2 > 0`
(SPL-NL), SPL-A at `τ = x₀` gives a smooth compactly supported `g ≠ 0` with
`(‖κ(x₀)‖ − ε)‖g₃‖₁ ≤ ‖R(g,1)‖ ≤ c‖g₃‖₁`, so `‖g₃‖₁ = 0`; `g₃` is continuous (`g` is `C^∞` and `g₃ = g‴` by uniqueness
of derivatives), so `g₃ = 0`, `g` is a polynomial of degree ≤ 2 with compact support, so `g = 0`: contradiction.

## 3. Open points for the route referee
- N8 tail chain (three integrations by parts on improper integrals); `277/400 = 0.6925 < 0.72197399`.
- N7 cost at the pin (session 15 measured 1.3 s of kernel time for an earlier 40-cell table with `decide +kernel`);
  fallback: per-cell `norm_num` lemmas.
- Other names checked at the pin (session 17): `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
  `intervalIntegral.norm_integral_le_of_norm_le`, `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`,
  `image_le_of_deriv_right_le_deriv_boundary`, `exists_hasDerivAt_eq_slope`, `Complex.sq_norm`,
  `Complex.normSq_apply`, `MeasureTheory.integral_eq_zero_iff_of_nonneg`. `intervalIntegral.integral_pow` and
  `Complex.abs_re_le_abs` do not exist at the pin.
- N5: which of the two proofs is cheaper in Lean.

## Revision after the route referee (2026-11-28; `review/2026-11-28-SPLN-LOC2-route-answers.md`)

Parts as proved (the table in section 1 named three propositions that the blueprint merged):
- `SplnTaylorFacts` (N1 + N2), `SplnSecondFacts` (N4), the small branch of `SplnBranchFacts`: agent T,
  `OscInt/Front/StationaryLeadingSharpTaylor.lean`. N1 by an explicit primitive of `(x − v)² E(v)/2` in one
  fundamental-theorem step, not by comparing second derivatives.
- The tail branch of `SplnBranchFacts`: agent L, `OscInt/Front/StationaryLeadingSharpTail.lean`, with one primitive
  `G(v) = E(v)(−iv⁻¹ − v⁻³ + 3iv⁻⁵)` that does the three integrations by parts at once on finite intervals; bound
  `‖κ₊ − L/2‖ ≤ 5/(2x³) + 3/x⁵` for `x ≥ 4`.
- `SplnInterpFacts` (N5, the convexity route), `SplnCellsFacts` (N3, N6, N7: the 40 cells by `decide +kernel` on a
  Boolean checker proved sound), `SplnLowerFacts` (N9), `SplnThirdPosFacts` (N10): agent C,
  `OscInt/Front/StationaryLeadingSharp{Interp,CellsCore,CellsData,Cells,Third}.lean`.
- SPL-NK comes from SPL-NU and the proved SPL-S (`OscInt.API.stationaryLeading`), not from SPL-I directly.
- `Real.pi_lt_d2` (π < 3.15) suffices for `‖L‖ ≤ 4/3` and `‖L‖/2 ≤ 63/100`; it lives in
  `Mathlib.Analysis.Real.Pi.Bounds`, which the parts import explicitly.
