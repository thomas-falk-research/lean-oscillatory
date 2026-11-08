# Brief: sanity theorems through the remaining API3 constants (answer to the adversarial review M1, M2)

Repository `/home/user/lean-oscillatory` (built; `export PATH=$HOME/.elan/bin:$PATH`). Write ONE file
`/tmp/sanity2/FamilySanity2.lean` (scratch; write nothing in the repository). First lines:

```lean
import OscInt.Front.FamilySanity
import OscInt.Front.ConvertSanity
namespace OscInt.API.FamilySanity
open OscInt.Statements OscInt.API.ConvertAux
```

Compile with `nice -n 10 lake env lean -DautoImplicit=false /tmp/sanity2/FamilySanity2.lean` from the repository root,
one Lean process at a time. Library rules as in `review/prompts/API3-sanity-brief.md` (no `sorry`, `private`,
`set_option` except `maxHeartbeats … in`, no `⊤` smoothness index, `#check` names first and remove the `#check`s).

## Rule
Every theorem about a statement of `OscInt/Statements/Family.lean` takes the statement constant as a HYPOTHESIS and
only applies it to concrete data (as in `OscInt/Front/FamilySanity.lean`, read it first and reuse its definitions
`kinkPhase`, `kinkU`, `L₀`, `signFamily`, …). The proofs of the statements exist (`OscInt.API.*`), but do not use
them here: the point is that a plant in a statement body breaks these discharges. Use proved conversion lemmas freely
(`OscInt.API.hessDet_eq_det`, `foldOrNondeg_iff`, `ConvertSanity` lemmas such as `genCubic`,
`iteratedFDeriv_two_genCubic_zero`, `third_genCubic`, `d4FE_hyps_generic`).

## Theorems (names fixed)
1. `nonStationaryLocal_family (h : NonStationaryLocalStatement)`: the arccos family
   `disp σ k = Real.arccos (σ.1 * cos k.1 + σ.2 * cos k.2)` with `E = ℝ × ℝ`, `V = {σ | |σ.1| + |σ.2| < 1}` (open),
   `S = closedBall 0 (1/4)` (compact, `S ⊊ V`: say why in the docstring; max norm), `U = univ`, any compact `K`, `c > 0`,
   `N`: conclude the FE-S2.1L bound for this family. `ContDiffOn` of the uncurried family on `V ×ˢ univ` comes only
   from `Real.contDiffOn_arccos` (a ready proof is in `/tmp/lead/ConsumerLocal.lean`, `disp_contDiffOn`; copy it).
   Docstring: plants caught (`S ⊆ V` reversed, `K ⊆ U` reversed — with `U = univ` the reversed inclusion fails for a
   bounded `K` — and `IsOpen V` replaced by `IsCompact V`), and plants NOT caught: any plant that WEAKENS a hypothesis
   (e.g. `V ×ˢ U` replaced by `S ×ˢ K`), because a conditional sanity theorem can only detect a hypothesis that
   became harder to discharge.
2. `stationaryPhaseLocal_kink (h : StationaryPhaseLocalStatement)` and `foldLocal_kink (h : FoldLocalStatement)`:
   the constant family `fun _ : ℝ => kinkPhase`, `S = {1}`, `V = Set.Ioo 0 2` (so `S ⊊ V`), `U = kinkU`,
   `K = closedBall 0 2`, `K' = {L₀}`; reuse `kink_det_ne` etc.
3. `d4BoundLocal_kink (h : D4BoundLocalStatement)`: `φ k = genCubic 1 2 3 5 k + |k.1 - 5| - 5 + k.1` (equal to the
   generic cubic on `U = {k | k.1 < 5}`, singular on `k.1 = 5`), coefficients `(1, 2, 3, 5)`: derivative hypotheses at
   0 by germ equality with `genCubic 1 2 3 5` and `d4FE_hyps_generic`. Also `d4Kink_not_contDiff`. Docstring: the
   coefficient order is pinned by `d4FE_reversed_fails`.
4. `nonStationaryOn_kink (h : NonStationaryOnStatement)`: `kinkPhase`, `K = closedBall 0 2`, `U = kinkU`, `c = 1`, `N`.
5. (adversarial M2) `stationaryPhaseFamily_binder_bite (h : StationaryPhaseFamilyStatement)`: one-point family
   `Unit`, `Ψ k = k.1 ^ 4 / 4 - 2 * k.1 ^ 3 + 9 / 2 * k.1 ^ 2 + k.2 ^ 2` (so `∂₁Ψ = x(x − 3)²`, `∂₁₁Ψ = 3(x − 1)(x − 3)`),
   `K = closedBall 0 1`, `K' = {(0, 0), (3, 0)}`. Critical points with `p = (0, 0)`: `(0, 0)` (nondegenerate,
   Hessian diag(9, 2), in K) and `(3, 0)` (degenerate, NOT in K). With `p = (3, 0)`: `x³ − 6x² + 9x + 3 = 0` has its
   roots away from `x ∈ {1, 3}` (the polynomial is 7 at 1 and 3 at 3), so the Hessian is nondegenerate at every
   critical point. Plants caught (docstring): `∀ k ∈ K` replaced by `∀ k ∈ K'`-as-points or by `∀ k` (the degenerate
   critical point `(3, 0)` enters), and "nondegenerate at every k ∈ K" is NOT caught here (say so; the sign bites
   catch it). Conclude the S2.2F bound for these data.
   Also `foldCrit_binder_bite (h : FoldCritStatement)` on the same data if `FoldOrNondeg` fails at `(3, 0)` (Hessian
   diag(0, 2), kernel e₁, third derivative `∂₁₁₁Ψ(3) = 6x − 12 = 6 ≠ 0` — so it IS a fold and the plant would NOT be
   caught for S3c; then do not write this theorem and say so in your report).

## Report
Final file verbatim, compile output (must be empty), and for each theorem the plants caught and not caught. Time box:
deliver what compiles and say where anything stopped.
