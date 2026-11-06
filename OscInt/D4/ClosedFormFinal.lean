import OscInt.D4.ClosedForm
import OscInt.D4.GammaSixth
import OscInt.D4.CosMomentValue
import OscInt.D4.Chart
import OscInt.D4.Covariance
import OscInt.D4.NormalForm
import OscInt.D4.Beta
import OscInt.D4.LineMoments

/-!
# S4.4: closed forms of the D4 constant

`OscInt.d4ConstantClosedForm : D4ConstantClosedFormStatement`: the improper integral `∫₀^∞ cos u · u^{-1/3} du`
equals `Γ(2/3)/2`, and `c_C = Γ(1/3)²/(√3 |Disc C|^{1/6})` for `Disc C < 0` (the brief's constant),
`c_C = Γ(1/3)²/(Disc C)^{1/6}` for `Disc C > 0`. Route `docs/proof-S44.md`; assembly
`OscInt.D4.d4ConstantClosedForm_of` (lead) from E1 (agent M), E2 (agent N), E3 (agent O), E5 (agent T),
E6a–c (agent K), E4 and E7 (lead). Together with S4.2 (`OscInt.d4Limit`) this is the brief's S4 limit
`t^{2/3} ∫ e^{itφ} A → Γ(1/3)²/(√3 |Disc|^{1/6}) · A(0)` for `Disc < 0`.

`d4Constant_example` evaluates the closed form on a cubic with all coefficients distinct and nonzero
(`x³ + 2x²y + 3xy² + 5y³`, `disc = −367`; lessons 17); numerically, `(1/3) · Γ(2/3)/2 · J(C)` computed from the
definition agrees with it to 2·10⁻⁹ (mpmath quadrature with breakpoints at the zeros; tooling, not evidence).
-/

namespace OscInt

open OscInt.Statements OscInt.D4

/-- **S4.4** -/
theorem d4ConstantClosedForm : D4ConstantClosedFormStatement :=
  d4ConstantClosedForm_of (cosMomentValue betaIoi) angularLine covariance normalForm
    (lineMomentValues betaIoi betaUnit) gammaSixth

/-- The closed form on generic data: `c_C` for `C = x³ + 2x²y + 3xy² + 5y³` (`disc = −367`). -/
theorem d4Constant_example :
    d4Constant (1, 2, 3, 5) = Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * (367 : ℝ) ^ ((1 : ℝ) / 6)) := by
  have hd : disc ((1 : ℝ), (2 : ℝ), (3 : ℝ), (5 : ℝ)) = -367 := by norm_num [disc]
  rw [d4ConstantClosedForm.2.1 _ (by rw [hd]; norm_num), hd]
  norm_num

end OscInt
