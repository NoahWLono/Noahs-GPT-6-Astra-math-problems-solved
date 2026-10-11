import Lean
import RUPPath.Inputs
open Lean Meta Elab Command
namespace RUPReplay
structure Step where
  id : Nat
  target : Array Int
  hints : Array (Nat × Array Int)
  deriving FromJson

def literal (p : Expr) (l : Int) : Expr :=
  let e := mkApp p (mkNatLit l.natAbs)
  if l > 0 then e else mkApp (mkConst ``Not) e

def clause (p : Expr) : List Int → Expr
  | [] => mkConst ``False
  | [l] => literal p l
  | l :: ls => mkApp2 (mkConst ``Or) (literal p l) (clause p ls)

def inject (p : Expr) (c : List Int) (idx : Nat) (t : Expr) : Expr :=
  match c, idx with
  | [_], 0 => t
  | l::ls, 0 => mkApp3 (mkConst ``Or.inl) (literal p l) (clause p ls) t
  | l::ls, i+1 => mkApp3 (mkConst ``Or.inr) (literal p l) (clause p ls) (inject p ls i t)
  | _, _ => t

def cname (id : Nat) : Name := .str (.str .anonymous "Q6RUPPath") ("c" ++ toString id)
def hypothesis (p h : Expr) (id : Nat) : Expr :=
  if id ≤ 1623 then
    let j := (id-1)/50
    let chunk := mkApp2 (mkConst (.str (.str (.str .anonymous "Q6RUPPath") "Inputs") ("chunk" ++ toString j))) p h
    mkApp2 (mkConst (.str (.str (.str .anonymous "Q6RUPPath") ("InputChunk" ++ toString j)) ("c" ++ toString id))) p chunk
  else mkApp2 (mkConst (cname id)) p h

abbrev Known := Std.HashMap Int Expr

def contradiction (known : Known) (l : Int) (t : Expr) : MetaM Expr := do
  let some opp := known[l.neg]? | throwError "missing opposing literal {l}"
  return if l > 0 then mkApp opp t else mkApp t opp

partial def eliminate (p : Expr) (known : Known) (ls : List Int) (major : Expr)
    (unit : Option Int) : MetaM Expr := do
  let target := match unit with | some l => literal p l | none => mkConst ``False
  match ls with
  | [] => return major
  | [l] =>
    if unit == some l then return major
    let bad ← contradiction known l major
    return if unit.isSome then mkApp2 (mkConst ``False.elim [.zero]) target bad else bad
  | l::rest =>
    let left ← withLocalDeclD `t (literal p l) fun t => do
      let body ← if unit == some l then pure t else do
        let bad ← contradiction known l t
        pure (if unit.isSome then mkApp2 (mkConst ``False.elim [.zero]) target bad else bad)
      mkLambdaFVars #[t] body
    let right ← withLocalDeclD `t (clause p rest) fun t => do
      let body ← eliminate p known rest t unit
      mkLambdaFVars #[t] body
    return mkApp6 (mkConst ``Or.elim) (literal p l) (clause p rest) target major left right

partial def propagate (p h : Expr) (known : Known) (hints : List (Nat × Array Int)) (k : Nat) : MetaM Expr := do
  match hints with
  | [] => throwError "RUP hints ended without conflict"
  | (id,c)::rest =>
    let unset := c.filter (fun l => !known.contains (-l))
    if c.any (fun l => known.contains l) then throwError "satisfied hint {id}"
    if unset.size > 1 then throwError "nonunit hint {id}"
    let unit := unset[0]?
    let proof ← eliminate p known c.toList (hypothesis p h id) unit
    match unit with
    | none => return proof
    | some l => withLetDecl (.str .anonymous ("k" ++ toString k)) (literal p l) proof fun v => do
      let body ← propagate p h (known.insert l v) rest (k+1)
      mkLetFVars #[v] body

partial def assumeNegation (p h n : Expr) (c : Array Int) (hints : List (Nat × Array Int))
    (i : Nat) (known : Known) : MetaM Expr := do
  if i < c.size then
    let l := c[i]!
    let neg ← withLocalDeclD `t (literal p l) fun t =>
      mkLambdaFVars #[t] (mkApp n (inject p c.toList i t))
    let value := if l > 0 then neg else mkApp2 (mkConst ``Classical.byContradiction) (literal p (-l)) neg
    withLetDecl (.str .anonymous ("n" ++ toString i)) (literal p (-l)) value fun v => do
      let body ← assumeNegation p h n c hints (i+1) (known.insert (-l) v)
      mkLetFVars #[v] body
  else propagate p h known hints 0

def replay (s : Step) : MetaM Unit := do
  let (type,value) ← withLocalDeclD `p (← mkArrow (mkConst ``Nat) (mkSort .zero)) fun p => do
    withLocalDeclD `h (mkApp (mkConst ``Q6RUPPath.Inputs) p) fun h => do
      let target := clause p s.target.toList
      let contra ← withLocalDeclD `n (mkApp (mkConst ``Not) target) fun n => do
        let body ← assumeNegation p h n s.target s.hints.toList 0 {}
        mkLambdaFVars #[n] body
      let body := mkApp2 (mkConst ``Classical.byContradiction) target contra
      return (← mkForallFVars #[p,h] target, ← mkLambdaFVars #[p,h] body)
  addDecl (.thmDecl { name := cname s.id, levelParams := [], type, value })

elab "replay_rup% " file:str : command => do
  let txt ← IO.FS.readFile file.getString
  let json ← IO.ofExcept (Json.parse txt)
  let steps ← IO.ofExcept (fromJson? (α := Array Step) json)
  liftTermElabM do
    for step in steps do replay step
  logInfo m!"Kernel checked {steps.size} RUP steps"
end RUPReplay
