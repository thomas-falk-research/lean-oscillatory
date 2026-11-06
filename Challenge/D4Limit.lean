import OscInt.Statements.D4Limit

/-! Frozen challenges for S4.1′, S4.2, S4.3, S4.4 (`lake comparator`). `sorry` by design; never imported, not
audited. One comparator configuration per theorem (`comparator-S41w.json`, `-S42`, `-S43`, `-S44`), so each is
judged as soon as it is proved. -/

namespace OscInt

theorem d4BoundNe : Statements.D4BoundNeStatement := sorry

theorem d4Limit : Statements.D4LimitStatement := sorry

theorem d4ConstantPos : Statements.D4ConstantPosStatement := sorry

theorem d4ConstantClosedForm : Statements.D4ConstantClosedFormStatement := sorry

end OscInt
