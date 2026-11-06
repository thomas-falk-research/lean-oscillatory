# Briefs for the S4.3 proof agents

## Common rules
As in `review/prompts/S1-briefs.md` (hard rules 1–7; replace `Blueprint.VanDerCorput` by `Blueprint.D4Limit`), with:
- Read first: `docs/proof-S43.md` including its final "Revision after the route referee" section (it overrides the
  text above it), `Blueprint/D4Limit.lean`, `OscInt/Statements/D4Limit.lean`, `GammaFree.lean`. Your file lives under
  `OscInt/D4/`; helpers in `namespace OscInt.D4.<Part>Aux` or `private`. The guard (`make guard`, allowed) forbids
  `open Lean`, `Lean.`-qualified names, `attribute`, `run_tac`, `set_option` except `set_option maxHeartbeats N in`,
  and `ContDiff ℝ ⊤` (write `∞` with `open scoped ContDiff`, or a numeral).
- **Gamma-free (pre-registered rule):** no constant whose name contains `Gamma`, `Beta`, `betaIntegral`, `mellin` or
  `Mellin` may occur in the transitive closure of your theorems. Check before reporting: copy `GammaFree.lean` to a
  scratch file, change `import OscInt` to `import OscInt.D4.<YourModule>`, and add `#assert_gamma_free <your theorem>`
  lines. If a lemma you need pulls such a constant in, find another route and say so; do not report a failing proof.
- Three agents share 4 CPUs and 15 GB: at most ONE Lean process each, always `nice -n 10`.
- If a part is false as stated, STOP and report a counterexample (rule 3). Do not weaken it.

## Task U: `OscInt/D4/CosMoment.lean` — `theorem OscInt.D4.cosIBP : OscInt.Blueprint.CosIBPFacts` and
`theorem OscInt.D4.sinMoment : OscInt.Blueprint.SinMomentFacts`
C1 by `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (route revision (2)). C2: integrability of
sin u · u^{−4/3} on `Ioi 0` (≤ u^{−1/3} on (0, 1] via `Real.abs_sin_le_abs`, ≤ u^{−4/3} on [1, ∞) via
`integrableOn_Ioi_rpow_of_lt`), then `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` for the limit S; S > 0 by
writing ∫₀^{2Nπ} as a sum of b_k (`intervalIntegral.sum_integral_adjacent_intervals`, `integral_comp_add_right`),
each b_k > 0 (`intervalIntegral.intervalIntegral_pos_of_pos_on`), and S = lim_N ∫₀^{2Nπ} ≥ b₀.

## Task V: `OscInt/D4/Angular.lean` — `theorem OscInt.D4.circleNondeg : OscInt.Blueprint.CircleNondegFacts` and
`theorem OscInt.D4.angularPos : OscInt.Blueprint.AngularPosFacts`
C3: compute `deriv (circleCubic q)` explicitly (HasDerivAt of the polynomial in cos, sin), reduce to
`OscInt.D4.GaugeAux.disc_eq_zero` (`OscInt/D4/Gauge.lean`) with z = v = ω (route revision (4)), or prove the
algebraic fact directly with `linear_combination`. C5: nonnegativity, a point among θ = π/4, π/2, 3π/4, π where the
cubic is nonzero (route referee), continuity, `intervalIntegral.integral_pos_iff_support_of_nonneg_ae`.

## Task W: `OscInt/D4/SingularPower.lean` — `theorem OscInt.D4.singularPower : OscInt.Blueprint.SingularPowerFacts`
Route C4 with revision (3): finitely many zeros on [a, b] (isolated by `deriv g x₀ ≠ 0`, compactness), near each
zero |g x| ≥ (|g′(x₀)|/2)|x − x₀| (mean value / `HasDerivAt` + continuity of `deriv g`), domination by
c^{−α}|x − x₀|^{−α} (integrable for α < 1, `intervalIntegral.intervalIntegrable_rpow'` after translating), and away
from the zeros |g| ≥ c > 0 so |g|^{−α} is bounded and continuous. A compactness covering argument over [a, b] is the
cleanest assembly (each point has a neighbourhood interval on which the integrand is integrable; finitely many cover).
