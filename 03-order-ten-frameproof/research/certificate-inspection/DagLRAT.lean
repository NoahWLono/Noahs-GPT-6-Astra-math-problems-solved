/-
Adapted from Mathlib.Tactic.Sat.FromLRAT.
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0; see LICENSE.mathlib and NOTICE.txt.
Modified for this project to share certificate proof declarations and
conjunction projections. The modifications are described in NOTICE.txt.
-/
import SharedLRAT

open Lean Elab Std.Internal
open Mathlib.Tactic.Sat

namespace IndependentLRAT

/-- Share the conjunction-projection proof at every visited formula-tree node.
This avoids rechecking a path from the full CNF for each referenced input. -/
partial def buildInputsDAG (arr : Array (Array Int)) (neededPrefix : Array Nat)
    (ctx : Expr) (name : Name) (start stop : Nat) (f p : Expr)
    (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause) (count : Nat) :
    MetaM (Std.HashMap Nat Mathlib.Tactic.Sat.Clause × Nat) := do
  if neededPrefix[start]! == neededPrefix[stop]! then return (db, count)
  let nodeName := name ++ Name.mkSimple s!"contains_{start}_{stop}"
  addDecl <| Declaration.thmDecl {
    name := nodeName, levelParams := [],
    type := mkApp2 (mkConst ``Sat.Fmla.subsumes) ctx f, value := p
  }
  let p := mkConst nodeName
  if stop - start == 1 then
    let c := f.appArg!
    let inputName := name ++ Name.mkSimple s!"input{stop}"
    addDecl <| Declaration.thmDecl {
      name := inputName, levelParams := [],
      type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx c,
      value := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx c p
    }
    let count := count + 1
    if count % 100 == 0 then reportProgress name s!"Kernel checked {count} DAG input inclusions"
    return (db.insert stop { lits := arr[start]!, expr := c, proof := mkConst inputName }, count)
  let mid := start + (stop - start) / 2
  let f₁ := f.appFn!.appArg!
  let f₂ := f.appArg!
  let p₁ := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx f₁ f₂ p
  let p₂ := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx f₁ f₂ p
  let (db, count) ← buildInputsDAG arr neededPrefix ctx name start mid f₁ p₁ db count
  buildInputsDAG arr neededPrefix ctx name mid stop f₂ p₂ db count

def fromLRATDAG (cnf lrat : String) (name : Name) : MetaM Expr := withOptions (Elab.async.set · false) do
  reportProgress name "Parsing input CNF"
  let Parsec.ParseResult.success _ (_, arr) := Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := buildConj arr 0 arr.size
  let ctxName := name ++ `formula
  addDecl <| Declaration.defnDecl {
    name := ctxName, levelParams := [], type := mkConst ``Sat.Fmla,
    value := ctx', hints := ReducibilityHints.regular 0,
    safety := DefinitionSafety.safe
  }
  let ctx := mkConst ctxName
  reportProgress name s!"Kernel checked formula definition: {arr.size} clauses"
  let Parsec.ParseResult.success _ steps := Parser.parseLRAT ⟨_, lrat.startPos⟩
    | throwError "parse LRAT failed"
  let mut needed : Std.HashSet Nat := {}
  for step in steps do
    if let LRATStep.add _ _ hints := step then
      for hint in hints do
        if hint.natAbs ≤ arr.size then needed := needed.insert hint.natAbs
  let mut neededCounts : Array Nat := #[0]
  let mut n : Nat := 0
  for i in [1:arr.size + 1] do
    if needed.contains i then n := n + 1
    neededCounts := neededCounts.push n
  reportProgress name s!"Parsed {steps.size} LRAT steps; {n} referenced inputs"
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let (initialDB, _) ← buildInputsDAG arr neededCounts ctx name 0 arr.size ctx' p {} 0
  let mut db := initialDB
  let mut count : Nat := 0
  for step in steps do
    match step with
    | LRATStep.del ds => db := ds.foldl (·.erase ·) db
    | LRATStep.add i ns pf =>
      let e := buildClause ns
      let proof ← match buildProofStep db ns pf ctx e with
        | Except.ok proof => pure proof
        | Except.error msg => throwError msg
      let stepName := name ++ Name.mkSimple s!"step{i}"
      addDecl <| Declaration.thmDecl {
        name := stepName, levelParams := [],
        type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx e, value := proof
      }
      count := count + 1
      if count % 100 == 0 then reportProgress name s!"Kernel checked {count} RUP lemmas"
      if ns.isEmpty then
        reportProgress name s!"Kernel checked all {count} RUP lemmas"
        return mkConst stepName
      db := db.insert i { lits := ns, expr := e, proof := mkConst stepName }
  throwError "failed to prove empty clause"

elab "dag_lrat_files " n:ident cnf:str lrat:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnfText ← IO.FS.readFile cnf.getString
  let lratText ← IO.FS.readFile lrat.getString
  Command.liftTermElabM <| withOptions (Elab.async.set · false) do
    let proof ← fromLRATDAG cnfText lratText name
    let type ← Lean.Meta.inferType proof
    addDecl <| Declaration.thmDecl { name, levelParams := [], type, value := proof }

end IndependentLRAT
