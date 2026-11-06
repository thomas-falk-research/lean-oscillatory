import OscInt

/-!
Proof-method check for S4.3 (pre-registered 2026-11-06, `review/2026-11-06-S4b-pre-proof-answers.md`, before any
proof exists). The brief requires `c_C ≠ 0` by the alternating-series argument "not relying on Mellin/Gamma
identities". `#assert_gamma_free T` follows the transitive closure of constants used by the type and the value of
`T` (through every definition and theorem proof) and fails if any constant's name has a component containing
`Gamma`, `Beta`, `betaIntegral`, `mellin` or `Mellin`. Baseline: the closure of the statement itself has none
(referee B, 33 082 constants). If a generic Mathlib lemma pulls such a constant in, the check fails and the proof
is restructured; exceptions need a new dated decision recorded before they are used. Before the theorem exists the
check prints SKIPPED. Negative control: `#assert_gamma_free_expect_fail Real.Gamma_pos_of_pos`.
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
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
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
#assert_gamma_free OscInt.Statements.D4ConstantPosStatement
#assert_gamma_free OscInt.d4ConstantPos
