import Lean
import Mathlib.Data.Fin.Basic

open Lean Meta Elab Tactic

namespace GPT6Astra

/-- Canonicalize concrete matrix indices and closed Boolean decisions before
Boolean reflection. The resulting hypothesis is accepted only by Lean's
definitional-equality check; no mathematical assertion is added. -/
elab "canonical_matrix_atoms " a:ident " at " h:ident : tactic => withMainContext do
  let matrix ← getFVarId a
  let hyp ← getFVarId h
  let matrixExpr := mkFVar matrix
  let indices := (List.finRange 10).toArray.map toExpr
  let atoms := indices.flatMap fun r => indices.map fun c => mkApp2 matrixExpr r c
  let original ← hyp.getType
  let normalized ← Meta.transform original (pre := fun e => do
    let e := e.consumeMData
    if e.getAppFn == matrixExpr && e.getAppNumArgs == 2 then
      let args := e.getAppArgs
      let row ← whnf (mkProj ``Fin 0 args[0]!)
      let col ← whnf (mkProj ``Fin 0 args[1]!)
      if let (some r, some c) := (← getNatValue? row, ← getNatValue? col) then
        if r < 10 && c < 10 then
          return .done atoms[r * 10 + c]!
    if e.isAppOfArity ``decide 2 && !e.hasFVar && !e.hasMVar then
      let value ← withTransparency .all (whnf e)
      if value.isConstOf ``Bool.true || value.isConstOf ``Bool.false then
        return .done value
    return .continue)
  let goal ← getMainGoal
  let goal ← goal.changeLocalDecl hyp normalized
  replaceMainGoal [goal]

end GPT6Astra
