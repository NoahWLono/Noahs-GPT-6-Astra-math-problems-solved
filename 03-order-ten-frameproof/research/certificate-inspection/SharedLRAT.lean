/-
Adapted from Mathlib.Tactic.Sat.FromLRAT.
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0; see LICENSE.mathlib and NOTICE.txt.
Modified for this project to share certificate proof declarations and
conjunction projections. The modifications are described in NOTICE.txt.
-/
import Mathlib.Tactic.Sat.FromLRAT

open Lean Elab Std.Internal
open Mathlib.Tactic.Sat

namespace IndependentLRAT

def reportProgress (name : Name) (message : String) : MetaM Unit := do
  IO.FS.writeFile s!"research/certificate-inspection/{name}.progress" message
  IO.eprintln message

/-- Construct ordinary kernel-checked theorem declarations for each RUP step.
Subsequent steps refer to constants, avoiding recursive inlining of proofs. -/
def fromLRATShared (cnf lrat : String) (name : Name) : MetaM Expr := withOptions (Elab.async.set · false) do
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
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  reportProgress name s!"Parsed {steps.size} LRAT steps"
  let mut db := (buildClauses arr ctx 0 arr.size ctx' p default).2
  let mut needed : Std.HashSet Nat := {}
  for step in steps do
    if let LRATStep.add _ _ hints := step then
      for hint in hints do
        if hint.natAbs ≤ arr.size then needed := needed.insert hint.natAbs
  let mut inputCount : Nat := 0
  for i in [1:arr.size + 1] do
    if !needed.contains i then
      db := db.erase i
      continue
    let some clause := db[i]? | throwError "missing input clause"
    let inputName := name ++ Name.mkSimple s!"input{i}"
    addDecl <| Declaration.thmDecl {
      name := inputName, levelParams := [],
      type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx clause.expr,
      value := clause.proof
    }
    db := db.insert i { clause with proof := mkConst inputName }
    inputCount := inputCount + 1
    if inputCount % 100 == 0 then reportProgress name s!"Kernel checked {inputCount} input inclusions"
  reportProgress name s!"Kernel checked {inputCount} input clause inclusions"
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

elab "shared_lrat_unsat " n:ident cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let cnf ← unsafe Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Term.evalTerm String (mkConst ``String) lrat
    let proof ← fromLRATShared cnf lrat name
    let type ← Lean.Meta.inferType proof
    addDecl <| Declaration.thmDecl { name, levelParams := [], type, value := proof }

-- Read untrusted source files directly; avoid compiling multi-megabyte string
-- literal terms. The formula and all proof declarations still undergo normal
-- kernel checking. This command certifies the decoded formula, not a file hash.
elab "shared_lrat_files " n:ident cnf:str lrat:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnfText ← IO.FS.readFile cnf.getString
  let lratText ← IO.FS.readFile lrat.getString
  Command.liftTermElabM do
    let proof ← fromLRATShared cnfText lratText name
    let type ← Lean.Meta.inferType proof
    addDecl <| Declaration.thmDecl { name, levelParams := [], type, value := proof }

elab "raw_lrat_files " n:ident cnf:str lrat:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnfText ← IO.FS.readFile cnf.getString
  let lratText ← IO.FS.readFile lrat.getString
  Command.liftTermElabM <| withOptions (Elab.async.set · false) do
    reportProgress name "Building raw LRAT proof"
    let (_, _, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux cnfText lratText name
    reportProgress name "Kernel checked raw LRAT proof"
    let type ← Lean.Meta.inferType proof
    addDecl <| Declaration.thmDecl { name, levelParams := [], type, value := proof }

end IndependentLRAT
