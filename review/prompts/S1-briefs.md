# Briefs for the S1 proof agents (van der Corput)

## Common rules for every proof agent

Repository: /home/user/lean-oscillatory (Lean v4.35.0, Mathlib 56a0058, already built; `export PATH="$HOME/.elan/bin:$PATH"`).
The lead has frozen, timestamped and had reviewed the statements `OscInt/Statements/VanDerCorput.lean` and written the
blueprint `Blueprint/VanDerCorput.lean` (definitions only, built). Read both files completely first. Your job is to
PROVE one blueprint proposition, exactly as stated, in your own new file.

Hard rules.
1. Write only your own file (named in your task) and scratch files under `/tmp/<your task letter>/`. Do not edit any
   other file; do not run `make`, `lake build` of the whole library, `git commit`, `git push`, or anything that
   changes git state.
2. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `@[extern]`, `opaque`, `macro`, `elab`,
   `syntax`, `notation`, `run_cmd`, `#eval`, `local instance`, or any `set_option` that weakens checking
   (`set_option maxHeartbeats N in` on a single declaration is allowed; report where). Only Mathlib and project modules.
3. Never weaken, reformulate or "fix" the proposition. If you believe it is false or unprovable as stated, STOP and
   report the exact problem with a counterexample or a precise explanation, and what you can prove instead.
4. Compile with `cd /home/user/lean-oscillatory && nice -n 10 lake env lean -DautoImplicit=false <file>`. At most ONE
   Lean process at a time (four agents share 4 CPUs and 15 GB). Develop in a scratch file importing
   `Blueprint.VanDerCorput`; move finished lemmas into your file. When the file is complete, `nice -n 10 lake build
   <Module.Name>` for your module only.
5. Done means: your file compiles with no errors and no `sorry` warning, and a temporary `#print axioms <main>` prints
   `[propext, Classical.choice, Quot.sound]` or a subset. Remove the `#print` line. Module docstring at the top (what
   the file proves and how, a few lines, crediting the source route); short docstrings on main lemmas. Declarations
   ≤ ~60 lines; split arithmetic into lemmas over ℝ.
6. Put helpers in `namespace OscInt.VanDerCorput.<PartName>Aux` or mark them `private`.
7. Final message: main theorem name and file, line count, the axiom output, any `maxHeartbeats`, reusable general
   lemmas (name + one-line statement), and any problem with the blueprint (rule 3). Claim nothing you did not run.

Mathlib names checked at the pin (all in namespace `intervalIntegral` unless prefixed):
`integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`, `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`,
`integral_eq_sub_of_hasDeriv_right`, `integral_eq_sub_of_hasDerivAt_of_le`, `integral_add_adjacent_intervals`,
`norm_integral_le_of_norm_le_const`, `norm_integral_le_integral_norm`, `norm_integral_le_abs_integral_norm`,
`integral_congr_ae`, `integral_hasDerivWithinAt_right`, `integral_hasDerivAt_right`, `integral_comp_neg`,
`intervalIntegral_conj` (full name `intervalIntegral.intervalIntegral_conj`); global: `MonotoneOn.intervalIntegrable_deriv`
(derivative of a function monotone on `uIcc a b` is interval integrable), `hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne`
(Darboux: a derivative never equal to m is always < m or always > m on a convex set), `Complex.norm_exp_ofReal_mul_I`,
`Complex.exp_conj`, `exists_hasDerivAt_eq_slope`, `intermediate_value_Icc`, `monotoneOn_of_deriv_nonneg`,
`strictMonoOn_of_deriv_pos`, `Convex.mul_sub_le_image_sub_of_le_deriv`, `IntervalIntegrable.norm`.
Pitfall: in this Mathlib `HasDerivAt` lemmas combine with `HasDerivAt.fun_add`, `.fun_mul` etc. (the `.add` form is
for `f + g`); import `Mathlib.Analysis.Calculus.Deriv.Add` or use `import Mathlib` in scratch files. Dot notation on a
`HasDerivAt` term can resolve to `HasFDerivAtFilter.*` if the `HasDerivAt.*` lemma is not imported: check imports.

Reference route: J. Roos and M. Praveen, `roos-j/lean-oscillatory`, file `LeanOscillatory/VanDerCorput.lean`
(Apache-2.0; https://raw.githubusercontent.com/roos-j/lean-oscillatory/cf564e0e100e91de222a53b85b106fa9a03a0ec5/LeanOscillatory/VanDerCorput.lean).
You may read it and adapt its proof ideas and tactic scripts. Its encoding differs (`ContDiffOn` on `[[a, b]]`,
`derivWithin`); ours uses explicit derivatives with `HasDerivOn` (continuous on `Icc`, `HasDerivAt` on `Ioo`) and
assumes nothing about the top derivative beyond existence. Credit it in your module docstring.

## Task A: `OscInt/VanDerCorput/Split.lean`, `theorem OscInt.VanDerCorput.splitFacts : OscInt.Blueprint.SplitFacts`

Sketch. If a = b take d = a. Otherwise Darboux (`hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne` on `Ioo a b`
with m = 0, using μ ≤ |g'| so g' ≠ 0) gives g' ≥ μ on (a,b) or g' ≤ −μ there. In the first case
`Convex.mul_sub_le_image_sub_of_le_deriv` (or the mean value theorem on subintervals, with continuity on `Icc`) gives
μ (y − x) ≤ g y − g x for x ≤ y in [a, b]; so g is monotone on [a, b]. Then: if g a ≥ 0 take d = a; if g b ≤ 0 take
d = b; else IVT gives d with g d = 0; in each case μ|x − d| ≤ |g x|. The second case follows by applying the first to
−g (or by symmetry). This is `exists_le_abs_of_le_derivWithin` in the reference.

## Task B: `OscInt/VanDerCorput/One.lean`, `theorem OscInt.VanDerCorput.vdc1Plain : OscInt.Blueprint.VdC1PlainFacts`

Sketch. Reduce to a < b. φ' is continuous on [a, b] and |φ'| ≥ ν on (a, b), hence on [a, b], and (Darboux or IVT) φ'
has one sign: φ' ≥ ν everywhere or φ' ≤ −ν. Antitone case: reduce to the monotone case by φ ↦ −φ (the integral is
conjugated; norms agree; use `intervalIntegral.intervalIntegral_conj` and `Complex.exp_conj`) — or handle both signs
directly; choose what is shorter. Integrate by parts with u = (i φ')⁻¹, v = e^{iφ}, v' = iφ' e^{iφ}, u' = iφ''/φ'²
(derivatives on (a, b); `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right` needs `ContinuousOn` on `uIcc` and
interval-integrable u', v'). Boundary terms ≤ 2/ν. Remainder: ‖∫ u' v‖ ≤ ∫ |φ''|/φ'² = |∫ (d/dx)(−1/φ')| =
|1/φ'(a) − 1/φ'(b)| ≤ 1/ν, using that −1/φ' is monotone (φ' monotone of one sign) and φ''/φ'² has a sign. The
integrability of φ''/φ'²: it is the derivative of the monotone function −1/φ' on (a, b), so
`MonotoneOn.intervalIntegrable_deriv` applies after an a.e. congruence (`deriv` of −1/φ' equals φ''/φ'² on (a, b)).
Total 3/ν. The reference proves this as `norm_integral_exp_mul_I_le_of_order_one'` under C².

## Task C: `OscInt/VanDerCorput/Amplitude.lean`, `theorem OscInt.VanDerCorput.amplitudeTransfer : OscInt.Blueprint.AmplitudeTransferFacts`

Sketch. Reduce to a < b. F(x) = ∫_a^x e^{iφ} has derivative e^{iφ(x)} on (a, b) (`integral_hasDerivAt_right`, the
integrand is continuous on [a, b]) and is continuous on [a, b]. Integrate by parts (`integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
or the `HasDerivAt` variant, with F' = e^{iφ} continuous hence integrable, ψ' integrable by hypothesis):
∫ e^{iφ} ψ = F(b)ψ(b) − F(a)ψ(a) − ∫ F ψ', F(a) = 0. Then ‖F(b)ψ(b)‖ ≤ C‖ψ b‖ and ‖∫ F ψ'‖ ≤ ∫ C‖ψ'‖. Mind the
order of factors: `oscInt φ ψ a b = ∫ exp(φ x * I) * ψ x`. The reference proves this as
`norm_integral_exp_mul_I_smul_le_of_norm_integral_exp_mul_I` (C¹ amplitude; ours needs only ψ' integrable).

## Task D: `OscInt/VanDerCorput/Higher.lean`, prove
`theorem OscInt.VanDerCorput.vdc2Plain (hS : OscInt.Blueprint.SplitFacts) (h1 : OscInt.Blueprint.VdC1PlainFacts) : OscInt.Blueprint.VdC2PlainFacts`
and
`theorem OscInt.VanDerCorput.vdc3Plain (hS : OscInt.Blueprint.SplitFacts) (h2 : OscInt.Blueprint.VdC2PlainFacts) : OscInt.Blueprint.VdC3PlainFacts`.

Sketch for k = 2. Apply `hS` to g = φ', g' = φ'': φ' monotone or antitone on [a, b] and ∃ d, μ|x − d| ≤ |φ' x|.
Let λ = √μ, c₁ = max a (d − λ/μ), c₂ = min b (d + λ/μ). Split ∫_a^b = ∫_a^{c₁} + ∫_{c₁}^{c₂} + ∫_{c₂}^b
(`integral_add_adjacent_intervals`; the integrand is continuous). Middle: ≤ c₂ − c₁ ≤ 2λ/μ (`norm_integral_le_of_norm_le_const`,
`Complex.norm_exp_ofReal_mul_I`). Outer pieces: on [a, c₁] (when a < c₁) every x has |x − d| ≥ λ/μ, so |φ'| ≥ λ;
apply `h1` on [a, c₁] with ν = λ (restrict `HasDerivOn` and monotonicity to the subinterval): ≤ 3/λ; same on [c₂, b].
Total 2λ/μ + 6/λ = 8/√μ for λ = √μ. Sketch for k = 3: same with g = φ'', g' = φ''', `h2` on the outer pieces with
μ := λ, λ = μ^{2/3}: total 2λ/μ + 2 · 8/√λ = 2μ^{-1/3} + 16μ^{-1/3} = 18 μ^{-1/3}. Write one private lemma for the
splitting (generic in the outer bound B(λ)) and use it twice. The reference does both at once by induction on k
(`norm_integral_exp_mul_I_le_of_order_ge_two'`). Real-power arithmetic: `Real.rpow_natCast`, `Real.sqrt_eq_rpow`,
`Real.rpow_add`, `Real.rpow_mul`, `Real.mul_rpow`; prove the two constant identities as separate lemmas first.
Numerical check of the interfaces: `numerics/results-2026-11-05.txt` Part 1 (k = 1, 2, 3 on subintervals and with
linear terms: worst ratios 0.53, 0.42, 0.25 of the constants).
