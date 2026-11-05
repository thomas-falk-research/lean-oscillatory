import OscInt.VanDerCorput.Assembly
import OscInt.VanDerCorput.Split
import OscInt.VanDerCorput.One
import OscInt.VanDerCorput.Amplitude
import OscInt.VanDerCorput.Higher

/-!
# S1: the one-dimensional van der Corput lemma (final theorems)

Each theorem's type is the frozen statement constant (checked by `StatementTypes.lean` and `lake comparator`).
Route ported from J. Roos and M. Praveen, `roos-j/lean-oscillatory` (Mathlib PR #39406), after Stein VIII §1.2.
-/

namespace OscInt

open VanDerCorput

theorem vanDerCorput_one : Statements.VdC1Statement := vdc1_of vdc1Plain amplitudeTransfer

theorem vanDerCorput_two : Statements.VdC2Statement :=
  vdc2_of (vdc2Plain splitFacts vdc1Plain) amplitudeTransfer

theorem vanDerCorput_three : Statements.VdC3Statement :=
  vdc3_of (vdc3Plain splitFacts (vdc2Plain splitFacts vdc1Plain)) amplitudeTransfer

end OscInt
