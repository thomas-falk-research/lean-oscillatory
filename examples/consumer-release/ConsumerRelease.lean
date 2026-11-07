import OscInt.API

/-!
# A downstream use of OscInt v0.3.0, pinned by tag

Uses only names on the stable surface of v0.3.0 (`docs/policy.md`): statement constants and the theorems that prove
them (`stamps/statements.json`, field `proved_by`), and the front-end theorems of `OscInt/API.lean`.
-/

open OscInt.Statements

theorem release_inputs : StationaryPhaseStatement ∧ FoldStatement ∧ D4LimitClosedFormStatement :=
  ⟨OscInt.stationaryPhase, OscInt.fold, OscInt.API.d4LimitClosedForm⟩
