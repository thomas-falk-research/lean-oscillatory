import Lean

/-!
Environment-side producer of statement commitments (the export-side producer is `tools/src/bin/commit.rs`;
both implement `docs/commitment-format.md` and must agree byte for byte).

Usage: `lake exe oscint-commit-env OUTDIR` writes, for every `def …Statement : Prop` declared in a module
under `OscInt.Statements`, the file `OUTDIR/<name>.env.txt`, and `OUTDIR/statements.txt` listing the names.
-/

open Lean

namespace CommitEnv

def encName : Name → String
  | .anonymous => ""
  | .str p s => encName p ++ s!"s{s.utf8ByteSize}:{s}"
  | .num p n => encName p ++ s!"n{n}."

def nameTok (n : Name) : String := "N" ++ encName n ++ ";"

structure EKey where
  e : Expr

instance : BEq EKey := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable EKey := ⟨fun a => a.e.hash⟩

structure St where
  lines : Array String := #[]
  lvlIds : Std.HashMap String Nat := {}
  exprIds : Std.HashMap String Nat := {}
  lvlMemo : Std.HashMap Level Nat := {}
  exprMemo : Std.HashMap EKey Nat := {}
  refs : NameSet := {}

abbrev M := StateM St

def intern (isLvl : Bool) (body : String) : M Nat := do
  let s ← get
  let tbl := if isLvl then s.lvlIds else s.exprIds
  match tbl[body]? with
  | some i => return i
  | none =>
    let i := tbl.size
    let tag := if isLvl then "L" else "E"
    if isLvl then
      set { s with lvlIds := s.lvlIds.insert body i, lines := s.lines.push s!"{tag}{i} {body}" }
    else
      set { s with exprIds := s.exprIds.insert body i, lines := s.lines.push s!"{tag}{i} {body}" }
    return i

partial def lvl (l : Level) : M Nat := do
  if let some i := (← get).lvlMemo[l]? then return i
  let body ← match l with
    | .zero => pure "z"
    | .succ a => return ← finish l s!"s {← lvl a}"
    | .max a b => do let i ← lvl a; let j ← lvl b; pure s!"m {i} {j}"
    | .imax a b => do let i ← lvl a; let j ← lvl b; pure s!"i {i} {j}"
    | .param n => pure s!"p {nameTok n}"
    | .mvar _ => panic! "level metavariable in a declaration"
  finish l body
where
  finish (l : Level) (body : String) : M Nat := do
    let i ← intern true body
    modify fun s => { s with lvlMemo := s.lvlMemo.insert l i }
    return i

def addRef (n : Name) : M Unit := modify fun s => { s with refs := s.refs.insert n }

partial def expr (e : Expr) : M Nat := do
  if let some i := (← get).exprMemo[EKey.mk e]? then return i
  let body ← match e with
    | .bvar k => pure s!"b {k}"
    | .sort u => do pure s!"S {← lvl u}"
    | .const n us => do
        addRef n
        let ids ← us.mapM lvl
        pure (s!"c {nameTok n} {ids.length}" ++ String.join (ids.map (s!" {·}")))
    | .app f a => do let i ← expr f; let j ← expr a; pure s!"a {i} {j}"
    | .lam _ t b _ => do let i ← expr t; let j ← expr b; pure s!"l {i} {j}"
    | .forallE _ t b _ => do let i ← expr t; let j ← expr b; pure s!"f {i} {j}"
    | .letE _ t v b _ => do
        let i ← expr t; let j ← expr v; let k ← expr b
        pure s!"t {i} {j} {k}"
    | .lit (.natVal v) => pure s!"n {v}"
    | .lit (.strVal v) => pure s!"r {v.utf8ByteSize}:{v}"
    | .mdata _ b => return ← expr b
    | .proj tn idx s => do addRef tn; let i ← expr s; pure s!"j {nameTok tn} {idx} {i}"
    | .fvar _ | .mvar _ => panic! "free variable or metavariable in a declaration"
  let i ← intern false body
  modify fun s => { s with exprMemo := s.exprMemo.insert (EKey.mk e) i }
  return i

def lps (ns : List Name) : String := s!"{ns.length}" ++ String.join (ns.map (s!" {nameTok ·}"))

def names (ns : List Name) : M String := do
  ns.forM addRef
  return s!"{ns.length}" ++ String.join (ns.map (s!" {nameTok ·}"))

/-- Serialises one constant; returns the declaration line. Proofs of theorems are not part of a commitment. -/
def decl (ci : ConstantInfo) : M String := do
  let hd := s!"{nameTok ci.name} {lps ci.levelParams} T {← expr ci.type}"
  match ci with
  | .axiomInfo v => return s!"D axiom {hd} {if v.isUnsafe then 1 else 0}"
  | .thmInfo _ => return s!"D thm {hd}"
  | .defnInfo v =>
    let sf := match v.safety with | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"
    return s!"D def {hd} V {← expr v.value} {sf}"
  | .opaqueInfo v => return s!"D opaque {hd} V {← expr v.value} {if v.isUnsafe then 1 else 0}"
  | .quotInfo v =>
    let k := match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
    return s!"D quot {hd} {k}"
  | .inductInfo v =>
    return s!"D induct {hd} {v.numParams} {v.numIndices} A {← names v.all} C {← names v.ctors} " ++
      s!"{if v.isRec then 1 else 0} {if v.isUnsafe then 1 else 0} {if v.isReflexive then 1 else 0} {v.numNested}"
  | .ctorInfo v =>
    addRef v.induct
    return s!"D ctor {hd} {nameTok v.induct} {v.cidx} {v.numParams} {v.numFields} {if v.isUnsafe then 1 else 0}"
  | .recInfo v =>
    return s!"D rec {hd} A {← names v.all} {v.numParams} {v.numIndices} {v.numMotives} {v.numMinors} " ++
      s!"{if v.k then 1 else 0} {if v.isUnsafe then 1 else 0}"

/-- Byte-wise order on the encoded names (the export-side producer sorts the same strings). -/
def nameLt (a b : Name) : Bool := (nameTok a).toUTF8.data.toList < (nameTok b).toUTF8.data.toList

def closure (env : Environment) (root : Name) : Except String (Array Name) := do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw s!"unknown constant {n}"
    let ((_ : String), st) := (decl ci).run {}
    for r in st.refs do
      unless seen.contains r do todo := todo.push r
  return (seen.toArray.qsort nameLt)

def commitment (env : Environment) (root : Name) : Except String String := do
  let cs ← closure env root
  let mut st : St := {}
  for n in cs do
    let some ci := env.find? n | throw s!"unknown constant {n}"
    let (line, st') := (decl ci).run st
    st := { st' with lines := st'.lines.push line, refs := {} }
  return "\n".intercalate (("OSCINT-COMMIT 1 " ++ nameTok root) :: st.lines.toList) ++ "\n"

end CommitEnv

open CommitEnv in
def main (args : List String) : IO UInt32 := do
  let [outDir] := args | IO.eprintln "usage: oscint-commit-env OUTDIR"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `OscInt }] {} (trustLevel := 0) (loadExts := false)
  let stmtModule (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (`OscInt.Statements).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let isStmt (n : Name) (ci : ConstantInfo) : Bool :=
    stmtModule n && (ci matches .defnInfo _) && ci.type == .sort .zero &&
      (match n with | .str _ s => s.endsWith "Statement" | _ => false)
  let stmts := (env.constants.fold (fun acc n ci => if isStmt n ci then acc.push n else acc) #[]).qsort nameLt
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir ++ "/statements.txt") (String.join (stmts.toList.map (s!"{·}\n")))
  for s in stmts do
    match commitment env s with
    | .ok txt => IO.FS.writeFile (outDir ++ s!"/{s}.env.txt") txt
    | .error msg => IO.eprintln msg; return 1
  IO.println s!"oscint-commit-env: {stmts.size} statement(s)"
  return 0
