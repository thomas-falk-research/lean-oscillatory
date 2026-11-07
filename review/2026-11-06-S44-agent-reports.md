# S4.4 proof-agent reports (verbatim)

Briefs: `review/prompts/S44-briefs.md`. Each report is the agent's final message, recorded without edits below its
heading. Lead's integration check for each part (2026-11-06): `lake build` of the module, forbidden-token scan,
the blueprint type pinned by `example`, `#print axioms` (`[propext, Classical.choice, Quot.sound]`), per-module
`leanchecker` (exit 0, no output). Agent run times: N 2.5 min, O 5.6 min, T 5.7 min, M 5.7 min.

## Agent N (E2, `OscInt/D4/Chart.lean`)

I've proved Task N in full: `theorem OscInt.D4.angularLine : OscInt.Blueprint.AngularLineFacts`, statement unchanged, in /home/user/lean-oscillatory/OscInt/D4/Chart.lean (98 lines).

**Checks I ran**
- `nice -n 10 lake env lean -DautoImplicit=false OscInt/D4/Chart.lean` gives no errors and no warnings.
- `nice -n 10 lake build OscInt.D4.Chart` reports "Build completed successfully".
- A temporary `#print axioms OscInt.D4.angularLine`, run in the scratch copy /tmp/N/A.lean and not in the final file, gives `[propext, Classical.choice, Quot.sound]`.
- `make guard` reports "ok: 55 file(s), 0 violations".
- No `maxHeartbeats` and no `set_option` anywhere. Every declaration is under 25 lines and no line is over 120 characters.

**Imports:** `Blueprint.D4ClosedForm`, `OscInt.D4.ConstantPosFinal` (for `OscInt.d4ConstantPos`), `OscInt.D4.Polar` (for `cubicForm_neg`), `Mathlib.MeasureTheory.Function.Jacobian`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv`. It does not depend on any other S4.4 part's file.

**Route:** E2 together with the revision's point 5.
1. The integrand is π-periodic because C(−z) = −C(z).
2. I split [0, 2π] at π. The interval integrability on each half comes from `(OscInt.d4ConstantPos.2.2 q hq).1` and `IntervalIntegrable.mono_set`.
3. `Function.Periodic.intervalIntegral_add_eq` turns each half into the integral over [−π/2, π/2].
4. That interval integral becomes a set integral over `Ioo (−π/2) (π/2)`, which equals `arctan '' univ`.
5. `integral_image_eq_integral_abs_deriv_smul` changes variables. It needs no integrability on ℝ, so it holds even though `lineMoment` is a Bochner integral.
6. A pointwise identity cancels the Jacobian, which finishes the proof.

**Helpers** (all in `namespace OscInt.D4.ChartAux`):
- `angF q θ := |cubicForm q (cos θ, sin θ)| ^ (-(2:ℝ)/3)`: the angular integrand.
- `angF_periodic q : Function.Periodic (angF q) π`.
- `rpow_cube_sqrt w (hw : 0 < w) : ((1 / √w) ^ 3) ^ (-(2:ℝ)/3) = w`.
- `chart_pointwise q u : |1 / (1 + u^2)| * angF q (arctan u) = |lineCubic q u| ^ (-(2:ℝ)/3)`.
- `chart_integral q : ∫ θ in -(π/2)..π/2, angF q θ = lineMoment q`. This holds for every q, with no disc hypothesis, and other parts could reuse it.

**Blueprint:** no problems found; the proposition is true as stated. The only files I wrote are Chart.lean and the scratch files under /tmp/N/. I made no git changes.

## Agent O (E3, `OscInt/D4/Covariance.lean`)

Task O is finished. `theorem OscInt.D4.covariance : OscInt.Blueprint.CovarianceFacts` is proved as stated in `/home/user/lean-oscillatory/OscInt/D4/Covariance.lean`, which is 167 lines long.

**Checks I ran**
- `nice -n 10 lake build OscInt.D4.Covariance` printed "Build completed successfully", with no errors and no `sorry` warnings.
- A temporary `#print axioms OscInt.D4.covariance` gave `[propext, Classical.choice, Quot.sound]`. I ran it on a scratch copy (`/tmp/O/CovAx.lean`), so the real file has no `#print` line.
- `make guard` printed "guard: ok: 58 file(s), 0 violations, 502 theorem declaration(s)".
- There is no `maxHeartbeats` and no `set_option`. Every declaration is under 30 lines.
- The file has a module docstring, which says which parts of `docs/proof-S44.md` the route follows (E3 and revision item 4).
- I edited no other file and made no git commits. The other changed or untracked files that `git status` shows were not made by me.

**Imports**
- Project: `OscInt.D4.CubicComp` (E4 by the lead, for `cubicForm_cubicComp` and `disc_cubicComp`), `OscInt.D4.PolarLimit` (`circleZerosNull`), `OscInt.D4.ConstantPosFinal` (`d4ConstantPos`) and `OscInt.D4.Polar` (`PolarAux.cubicForm_polar`).
- Mathlib: specific modules only, not all of Mathlib.
- It imports none of the other new S4.4 files (Chart, CosMomentValue, NormalForm). The one S4.4 dependency is E4, which the lead already proved; the brief lists it as reading. If that counts against the "no other S4.4 part" rule, the two lemmas I use are each a few lines of `ring` and could be copied in.

**How the proof goes**
- Put G(C) = ∫⁻ exp(−|C(z)|^{2/3}) over ℝ². By polar coordinates and Tonelli, done in `lintegral` form so no integrability conditions arise until the end, G(C) = J(C)/2.
- The zero set of the angular cubic is null by `circleZerosNull`. Shifting by one period (2π) moves the angular integral from (−π, π) to (0, 2π).
- A linear change of variables gives G(C ∘ g) = |det g|⁻¹ G(C).
- E4b shows the discriminant of C ∘ g is non-zero, and since `ENNReal.ofReal` is injective on non-negative reals, the result follows.

**Reusable lemmas** (all in `OscInt.D4.CovarianceAux`)
- `angInt q θ` and `wt q z` are local definitions: the angular integrand and the weight exp(−|C|^{2/3}) as an extended non-negative value.
- `lintegral_radial`: for 0 < a, ∫⁻ over r in (0, ∞) of r·e^{−a r²} is `ofReal ((2a)⁻¹)`.
- `abs_cubic_polar_rpow`: for r > 0, |C(r cos θ, r sin θ)|^{2/3} = |C(cos θ, sin θ)|^{2/3} · r².
- `angInt_periodic`: the angular integrand has period 2π.
- `angularMoment_Ioo`: if disc q ≠ 0, the integrand is integrable on (−π, π) and `angularMoment q` equals its integral there.
- `lintegral_wt`: if disc q ≠ 0, ∫⁻ of `wt q` over ℝ² is `ofReal (angularMoment q / 2)`.
- `lintegral_wt_comp`: if det2 g ≠ 0, ∫⁻ of `wt (cubicComp q g)` is `ofReal |det2 g|⁻¹` times ∫⁻ of `wt q`.

**Blueprint problems:** none. The Prop is true as stated and the route worked as written.

## Agent T (E5, `OscInt/D4/NormalForm.lean`)

Task T is done. `theorem OscInt.D4.normalForm : OscInt.Blueprint.CubicNormalFormFacts` is proved exactly as stated, in /home/user/lean-oscillatory/OscInt/D4/NormalForm.lean (197 lines). It imports only `OscInt.D4.CubicComp` (E4, which the lead proved); it does not import any other S4.4 part.

**Checks I ran:**
- **Axioms:** a temporary copy at /tmp/T/Final.lean with `#print axioms OscInt.D4.normalForm` printed `[propext, Classical.choice, Quot.sound]`. The file itself has no `#print`.
- **Compile and build:** `nice -n 10 lake env lean -DautoImplicit=false` gave no errors and no `sorry`. `nice -n 10 lake build OscInt.D4.NormalForm` reported "Build completed successfully".
- **Guard:** `make guard` reported "ok: 58 file(s), 0 violations".
- **Rules:** no `maxHeartbeats` and no `set_option`. I edited no other file and made no git changes. The other modified or untracked files in `git status` are not mine.

**Route (E5 steps 1–4, revision item 7):**
1. **Zero on the circle:** C(−z) = −C(z), so g(π) = −g(0). `intermediate_value_Icc'` or `intermediate_value_Icc` (chosen by the sign of q.1) gives a zero θ₀ in [0, π].
2. **Rotation:** the rotation (sin θ₀, cos θ₀, −cos θ₀, sin θ₀) has det 1 and makes the y³ coefficient 0.
3. **Shear:** `disc_cubicComp` keeps the discriminant, and disc(a,b,c,0) = 0 when c = 0, so c ≠ 0. The shear (1, 0, −b/(2c), 1) then gives (A, 0, C, 0) with disc = −4AC³.
4. **Scaling:** I scale by (α, 0, 0, β), with α³ = 1/A and β = 1/√(ε·C·α), to get (1, 0, ε, 0), where ε = ±1 has the sign of A·C.
   - The cube root is never `Real.rpow` of a negative base. It is `y^(1/3)` for y ≥ 0, and `-((-x)^(1/3))` for x < 0.
   - The brief suggested writing it as `sign a₂ * |a₂|^(-1/3)`; I used this existence form instead, which has the same effect.
5. **disc > 0 case:** x(x² − y²) composed with (1, 1, 1, −1) gives (0, 4, 4, 0), then scaling by γ with γ³ = 1/4 gives (0, 1, 1, 0).

Each step of composition uses `cubicComp_cubicComp` and `det2_mul`.

**Reusable lemmas** (all in `OscInt.D4.NormalFormAux`):
- `mul g h`: the explicit 2×2 matrix product on ℝ×ℝ×ℝ×ℝ.
- `lin2_mul`: `lin2 (mul g h) z = lin2 g (lin2 h z)`.
- `cubicComp_cubicComp`: `cubicComp (cubicComp q g) h = cubicComp q (mul g h)`.
- `det2_mul`: `det2 (mul g h) = det2 g * det2 h`.
- `exists_circle_zero`: `∃ θ, cubicForm q (cos θ, sin θ) = 0`, for any q.
- `exists_cube_eq`: `∃ α : ℝ, α ^ 3 = x`.
- `reduce`: `disc q ≠ 0 → ∃ g A C, det2 g = 1 ∧ cubicComp q g = (A, 0, C, 0) ∧ C ≠ 0 ∧ disc q = -4 * A * C ^ 3`.
- `rotate`, `shear`, `scale`, `scale_to`, `scale_four`, `hyperbolic`: one lemma per step above, each with its determinant.

**Blueprint problems:** none. The Prop is true as stated and the route went through unchanged.

## Agent M (E1, `OscInt/D4/CosMomentValue.lean`)

Task M is done. `theorem OscInt.D4.cosMomentValue (hB : OscInt.Blueprint.BetaIoiFacts) : OscInt.Blueprint.CosMomentValueFacts` is proved exactly as stated, in the new file `/home/user/lean-oscillatory/OscInt/D4/CosMomentValue.lean` (242 lines). It imports only `Blueprint.D4ClosedForm` and uses no other S4.4 part.

**Checks I ran:**
- `nice -n 10 lake env lean -DautoImplicit=false` on the file: no errors, no warnings, no `sorry`.
- `nice -n 10 lake build OscInt.D4.CosMomentValue`: "Build completed successfully".
- Temporary `#print axioms OscInt.D4.cosMomentValue` (in the scratch copy `/tmp/M/A.lean`, identical except the docstring, and removed before copying): `[propext, Classical.choice, Quot.sound]`.
- `make guard`: "ok: 58 file(s), 0 violations".
- No `maxHeartbeats` and no other `set_option`.

**Route:** E1 as in `docs/proof-S44.md`, with revision 3; it worked without any change.
1. The Gamma representation comes from `Real.integral_rpow_mul_exp_neg_mul_Ioi`.
2. Fubini uses `integral_integral_swap` on `(volume.restrict (Ioc 0 R)).prod (volume.restrict (Ioi 0))`; integrability is via `integrable_prod_iff`. The inner integral is finite because its integral is nonzero (`Integrable.of_integral_ne_zero`).
3. The inner u-integral is evaluated with `integral_eq_sub_of_hasDerivAt`, using the antiderivative e^{-us}(sin u − s cos u)/(1+s²).
4. R → ∞ uses `tendsto_integral_filter_of_dominated_convergence` with the bound s^{-2/3}(2s+1)/(1+s²). The bound is integrable: it is ≤ 2s^{-2/3} on (0,1] and ≤ 3s^{-5/3} on (1,∞).
5. The limit integral is computed with `integral_comp_rpow_Ioi_of_pos` (p = 2) and `hB` at a = 2/3, b = 1/3, then `Real.Gamma_one`; the conclusion follows from `Tendsto.limUnder_eq`.

**Helper lemmas**, all in `namespace OscInt.D4.CosMomentValueAux`; the first five may be reusable:
- `integral_gammaRep`: for 0 < u, `∫ s in Ioi 0, s^(-2/3) * exp(-(u*s)) = u^(-1/3) * Γ(1/3)`.
- `integrableOn_gammaRep`: for 0 < u, `s ↦ s^(-2/3) * exp(-(u*s))` is integrable on `Ioi 0`.
- `integral_cos_mul_exp` (any s, R): `∫ u in 0..R, cos u * exp(-(u*s)) = (s + exp(-(R*s)) * (sin R - s*cos R)) / (1 + s^2)`.
- `gamma_mul_cosMomentPartial`: for 0 ≤ R, `Γ(1/3) * cosMomentPartial R = ∫ s in Ioi 0, s^(-2/3) * h_R(s)`.
- `integral_limit`: given `BetaIoiFacts`, `∫ s in Ioi 0, s^(-2/3) * (s/(1+s^2)) = Γ(2/3) * Γ(1/3) / 2`.
- The rest only support this proof: `gamma_third_pos`, `integrable_fubini`, `abs_hR_num_le`, `bound`, `integrableOn_bound`, `tendsto_integral_hR`.

**Blueprint:** no problems; E1 is true as stated and proved without weakening.

I edited no other file and made no git operations. `git status` also shows changes I did not make (to `.gitignore`, `Makefile`, `tools/…`, and the other agents' `Chart`/`Covariance`/`NormalForm` files); I did not touch them.

## Agent K (E6a, E6b, E6c, `OscInt/D4/Beta.lean`, `OscInt/D4/LineMoments.lean`)

Run interrupted by a container restart and resumed from its transcript (9.5 min in total). Route change, recorded in
`docs/proof-S44.md`: E6a by the substitution x = t/(1+t) from E6b instead of Tonelli; statement unchanged. Lead's
integration check as above, plus the final theorem `OscInt.d4ConstantClosedForm` (type check, axioms, `leanchecker`
of `ClosedFormFinal`, `ClosedForm`, `CubicComp`, `GammaSixth`, `Beta`, `LineMoments`).

Task K is done. All three theorems are proved exactly as stated, the build succeeds and `make guard` passes. One change from the route: I proved E6a (`betaIoi`) by a change of variables from E6b, not by the Tonelli argument in the route doc.

**Files** (new and untracked; nothing else edited, no commit):
- `/home/user/lean-oscillatory/OscInt/D4/Beta.lean`, 100 lines.
  - `OscInt.D4.betaUnit : OscInt.Blueprint.BetaUnitFacts` (E6b).
  - `OscInt.D4.betaIoi : OscInt.Blueprint.BetaIoiFacts` (E6a).
- `/home/user/lean-oscillatory/OscInt/D4/LineMoments.lean`, 129 lines.
  - `OscInt.D4.lineMomentValues (hB : BetaIoiFacts) (hU : BetaUnitFacts) : LineMomentValuesFacts` (E6c).
  - It does not import `Beta.lean`; it uses E6a and E6b only as the hypotheses `hB` and `hU`. Its imports are `Blueprint.D4ClosedForm` and two Mathlib modules.

**Checks run:**
- `#print axioms` on a temporary copy of each file (the `#print` lines are not in the real files) gave `[propext, Classical.choice, Quot.sound]` for `betaIoi`, `betaUnit` and `lineMomentValues`.
- `nice -n 10 lake build OscInt.D4.Beta OscInt.D4.LineMoments`: "Build completed successfully", with no `sorry` warnings.
- `make guard`: "ok: 60 file(s), 0 violations".
- No `maxHeartbeats` or other `set_option` anywhere.

**How each part is proved:**
- **E6b:** uses `Complex.Gamma_mul_Gamma_eq_betaIntegral`. On `[0, 1]` the complex integrand is rewritten as the real one with `Complex.ofReal_cpow`, then `intervalIntegral.integral_ofReal`, `Complex.Gamma_ofReal`, and division by Γ(a+b) > 0.
- **E6a (the change from the route):** substitute x = t/(1+t), which maps (0, ∞) onto (0, 1) with dx = dt/(1+t)², and apply E6b, using `integral_image_eq_integral_abs_deriv_smul` and `integral_Ioc_eq_integral_Ioo`. This avoids the measurability and `lintegral` bookkeeping of the Tonelli argument. The statement is unchanged, and both theorems are in the same file, so no cross-part dependency arises.
- **E6c, the 1 + u² case:** follows the route, item 6. `integral_comp_abs` turns the integral over ℝ into twice the integral over (0, ∞). Then `integral_comp_rpow_Ioi_of_pos` with p = 2, `hB (1/2) (1/6)` and `Real.Gamma_one_half_eq`.
- **E6c, the u + u² case:** ℝ is split as Iic(−1), Ioc(−1, 0] and Ioi 0, using `intervalIntegral.integral_Iic_add_Ioi`, `Ioc_union_Ioi_eq_Ioi` and `setIntegral_union`.
  - On Ioi 0 it is `hB (1/3) (1/3)`.
  - On Iic(−1) the reflection u ↦ −1−u reduces it to Ioi 0, via `integral_image_eq_integral_abs_deriv_smul` and `integral_Iic_eq_integral_Iio`.
  - On (−1, 0) the substitution u ↦ −u (`intervalIntegral.integral_comp_neg`) and `hU (1/3) (1/3)` finish it.
  - Each piece is integrable because its value is positive and so nonzero (`Integrable.of_integral_ne_zero`, `intervalIntegral.intervalIntegrable_of_integral_ne_zero`).

**Helpers and reusable lemmas:**
- Public in `OscInt.D4`:
  - `lineMomentPlus (hB) : lineMoment (1,0,1,0) = √π Γ(1/6)/Γ(2/3)`
  - `lineMomentMinus (hB) (hU) : lineMoment (0,1,1,0) = 3 Γ(1/3)²/Γ(2/3)`
- In `OscInt.D4.BetaAux`:
  - `img`: (t ↦ t/(1+t)) maps Ioi 0 onto Ioo 0 1.
  - `injOn'`: that map is injective on Ioi 0.
  - `deriv'`: its derivative at t is 1/(1+t)².
  - `pointwise`: the Jacobian identity for the substitution.
- In `OscInt.D4.LineMomentsAux`:
  - `fm u = |u+u²|^(-2/3)`.
  - `fm_reflect`: fm(−1−x) = fm x.
  - `fm_pos`, `fm_neg`: closed forms of `fm` on (0, ∞) and on [0, 1] reflected.
  - `I1`, `I2`, `I3`: the three piece integrals.
  - `K1pt`: the pointwise identity for the u = √t substitution.

**Blueprint:** no problems found.

Scratch files are in `/tmp/K/`.
