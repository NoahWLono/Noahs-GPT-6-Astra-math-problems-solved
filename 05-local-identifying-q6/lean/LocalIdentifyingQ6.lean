import Std

/-! Q6 local identifying codes. No external axioms and no `native_decide`. -/
namespace LocalIdentifyingQ6
abbrev Vertex := Fin 64
abbrev Code := Vertex → Bool

def vertices : List Vertex := List.finRange 64

def adjacent (u v : Vertex) : Bool :=
  [1, 2, 4, 8, 16, 32].contains (Nat.xor u.val v.val)

def closed (u v : Vertex) : Bool := (u == v) || adjacent u v

def signature (C : Code) (u : Vertex) : Vertex → Bool := fun x => C x && closed u x

def Dominating (C : Code) : Prop := ∀ u, ∃ x, C x = true ∧ closed u x = true

def LocalIdentifying (C : Code) : Prop :=
  Dominating C ∧ ∀ u v, adjacent u v = true → signature C u ≠ signature C v

def EdgeHit (C : Code) (u v : Vertex) : Prop :=
  ∃ x, C x = true ∧ closed u x ≠ closed v x

def Constraints (C : Code) : Prop :=
  Dominating C ∧ ∀ u v, adjacent u v = true → EdgeHit C u v

theorem signatures_differ_iff (C : Code) (u v : Vertex) :
    signature C u ≠ signature C v ↔ EdgeHit C u v := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    funext x
    have hx : ¬(C x = true ∧ closed u x ≠ closed v x) := by
      intro hh
      exact hn ⟨x, hh⟩
    simp only [signature]
    cases hc : C x <;> simp_all
  · rintro ⟨x, hc, hd⟩ h
    have he := congrFun h x
    simp only [signature, hc, Bool.true_and] at he
    exact hd he

theorem localIdentifying_iff_constraints (C : Code) :
    LocalIdentifying C ↔ Constraints C := by
  simp only [LocalIdentifying, Constraints, signatures_differ_iff]

def witnessVertices : List Vertex :=
  [0, 4, 15, 23, 26, 29, 31, 33, 35, 36, 41, 49, 58, 62]

def witness : Code := fun x => witnessVertices.contains x

def cardinality (C : Code) : Nat := (vertices.filter C).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness_constraints : Constraints witness := by
  unfold Constraints Dominating EdgeHit
  decide

theorem witness_localIdentifying : LocalIdentifying witness :=
  (localIdentifying_iff_constraints witness).mpr witness_constraints

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness_cardinality : cardinality witness = 14 := by decide

#print axioms witness_localIdentifying
#print axioms witness_cardinality
#print axioms localIdentifying_iff_constraints
end LocalIdentifyingQ6
