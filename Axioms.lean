import OscInt

/-!
Axiom audit. `#audit_axioms` enumerates every theorem declared (with source position) in a module whose name is
`OscInt` or starts with `OscInt.`, except structure projections (generated for `Prop` fields: kernel projections,
no axioms, and no `theorem` keyword for the guard to count), prints one `AUDIT <name> <axioms>` line each (`<axioms>` is `none` or a
comma-separated list, the content of `#print axioms`), then `AUDIT-TOTAL <n> <clean>`. It fails unless every
theorem uses a subset of {propext, Classical.choice, Quot.sound}. `tools/src/bin/audit.rs` checks the output and
that `<n>` equals the number of `theorem`/`lemma` declarations the guard counts in the sources.

Limits (adversarial review 2026-11-06): this audit is not independent of the kernel replay. A metaprogram can add a
theorem without source position (not enumerated) and with kernel checking switched off; only `leanchecker` per
module, the export kernels and `lake comparator` reject that, and the guard forbids the metaprogramming needed.
Excluding projections cannot hide axioms from a final theorem: its transitive axiom set and its kernel replay
include everything it uses.
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let permitted : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ours (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (`OscInt).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if ours n && (ci matches .thmInfo _) && !n.isInternalDetail && !env.isProjectionFn n then
      if (← findDeclarationRanges? n).isSome then thms := thms.push n
  thms := thms.qsort Name.lt
  let mut clean := 0
  for n in thms do
    let axs := (← liftCoreM (collectAxioms n)).qsort Name.lt
    let ok := axs.all (permitted.contains ·)
    if ok then clean := clean + 1
    let shown := if axs.isEmpty then "none" else ",".intercalate (axs.toList.map toString)
    IO.println s!"AUDIT {n} {shown}"
  IO.println s!"AUDIT-TOTAL {thms.size} {clean}"
  if clean != thms.size then throwError "axiom audit failed: {thms.size - clean} theorem(s) use other axioms"

#audit_axioms
