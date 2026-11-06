import OscInt

/-!
Proof-method check for S4.3. The brief requires `c_C ≠ 0` by the alternating-series argument "not relying on
Mellin/Gamma identities". `#assert_gamma_free T` follows the transitive closure of the constants used by the type and
the value of `T`, through every definition, theorem proof and opaque value (`value? (allowOpaque := true)`), and
fails if any constant's name has a component containing `Gamma`, `Beta`, `betaIntegral`, `mellin` or `Mellin`.
The criterion is by name: a special-function identity re-proved under neutral names would pass, so the reviewed
route (integration by parts, then pairing the humps of sin u · u^{-4/3}) is part of the evidence.

History (lesson 18): a first version was committed in 94f7657 before any proof existed, but its `value?` skipped
theorem values, so it never followed proofs; the corrected check and the proof-only control below were introduced
in e89b610, the commit that added the S4.3 proof, and were re-run independently by the S4.1′–S4.3 adversarial
referee. Closure sizes count every constant reached (types and values); the statement's closure is 33 099.
Negative controls: `Real.Gamma_pos_of_pos` (Gamma in the type) and `gammaProofControl` (Gamma only in the proof);
both must be rejected. Exceptions need a new dated decision recorded before they are used.
-/

open Lean Elab Command

def gammaForbidden (n : Name) : Bool :=
  n.components.any fun c =>
    let s := c.toString
    ["Gamma", "Beta", "betaIntegral", "mellin", "Mellin"].any fun p => (s.splitOn p).length > 1

def gammaClosureBad (env : Environment) (n : Name) : Array Name × Nat := Id.run do
  let mut seen : NameHashSet := {}
  let mut stack : Array Name := #[n]
  let mut bad : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if gammaForbidden c then bad := bad.push c
    if let some ci := env.find? c then
      -- `value? (allowOpaque := true)`: in this Lean version plain `value?` returns `none` for theorems, which
      -- made the first version of this check skip every proof (lesson 18; control `gammaProofControl` below).
      let used := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      for d in used do
        unless seen.contains d do stack := stack.push d
  return (bad, seen.size)

elab "#assert_gamma_free " thm:ident : command => do
  let n := thm.getId
  let env ← getEnv
  if (env.find? n).isNone then
    IO.println s!"GAMMA-FREE SKIPPED {n} (not declared yet)"
  else
    let (bad, total) := gammaClosureBad env n
    unless bad.isEmpty do
      throwError m!"Gamma-free check FAILED for {n}: {bad.size} forbidden constant(s), e.g. {bad.toList.take 5}"
    IO.println s!"GAMMA-FREE OK {n} ({total} constants in the closure)"

elab "#assert_gamma_free_expect_fail " thm:ident : command => do
  let n := thm.getId
  let (bad, _) := gammaClosureBad (← getEnv) n
  if bad.isEmpty then throwError m!"negative control FAILED: no forbidden constant found for {n}"
  IO.println s!"GAMMA-FREE CONTROL {n} rejected as expected ({bad.size} forbidden constant(s))"

#assert_gamma_free_expect_fail Real.Gamma_pos_of_pos

/-- Control whose *type* is Gamma-free and whose *proof* uses `Real.Gamma`: the check must reject it. -/
theorem gammaProofControl : (0 : ℝ) < 1 := by
  have := Real.Gamma_pos_of_pos (one_pos : (0 : ℝ) < 1)
  norm_num

#assert_gamma_free_expect_fail gammaProofControl
#assert_gamma_free OscInt.Statements.D4ConstantPosStatement
#assert_gamma_free OscInt.d4ConstantPos
#assert_gamma_free OscInt.d4Limit
#assert_gamma_free OscInt.d4BoundNe
