module

public import Std

public section

/-! Exact predicates for the two activated finite problems. -/
namespace ExactCubeCodes

abbrev Vertex (d : Nat) := Fin (2^d)
abbrev Code (d : Nat) := Vertex d → Bool

@[expose] def vertices (d : Nat) : List (Vertex d) := List.finRange (2^d)
@[expose] def adjacent {d : Nat} (u v : Vertex d) : Bool :=
  ((List.range d).map (fun i => 2^i)).contains (u.val ^^^ v.val)
@[expose] def closed {d : Nat} (u v : Vertex d) : Bool := (u == v) || adjacent u v
@[expose] def signature {d : Nat} (C : Code d) (u : Vertex d) : Vertex d → Bool :=
  fun x => C x && closed u x
@[expose] def cardinality {d : Nat} (C : Code d) : Nat := ((vertices d).filter C).length

@[expose] def Dominating {d : Nat} (C : Code d) : Prop :=
  ∀ u, ∃ x, C x = true ∧ closed u x = true
@[expose] def Hit {d : Nat} (C : Code d) (u v : Vertex d) : Prop :=
  ∃ x, C x = true ∧ closed u x ≠ closed v x
@[expose] def LocalIdentifying {d : Nat} (C : Code d) : Prop :=
  Dominating C ∧ ∀ u v, adjacent u v = true → signature C u ≠ signature C v
@[expose] def OrdinaryLocatingDominating {d : Nat} (C : Code d) : Prop :=
  Dominating C ∧ ∀ u v, u ≠ v → C u = false → C v = false →
    signature C u ≠ signature C v
@[expose] def LocalConstraints {d : Nat} (C : Code d) : Prop :=
  Dominating C ∧ ∀ u v, adjacent u v = true → Hit C u v
@[expose] def LDConstraints {d : Nat} (C : Code d) : Prop :=
  Dominating C ∧ ∀ u v, u ≠ v → C u = false → C v = false → Hit C u v

theorem signatures_differ_iff {d : Nat} (C : Code d) (u v : Vertex d) :
    signature C u ≠ signature C v ↔ Hit C u v := by
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

theorem local_iff_constraints {d : Nat} (C : Code d) :
    LocalIdentifying C ↔ LocalConstraints C := by
  simp only [LocalIdentifying, LocalConstraints, signatures_differ_iff]

theorem ld_iff_constraints {d : Nat} (C : Code d) :
    OrdinaryLocatingDominating C ↔ LDConstraints C := by
  simp only [OrdinaryLocatingDominating, LDConstraints, signatures_differ_iff]

theorem adjacent_symmetric {d : Nat} (u v : Vertex d) :
    adjacent u v = adjacent v u := by
  simp only [adjacent, Nat.xor_comm]

theorem closed_symmetric {d : Nat} (u v : Vertex d) : closed u v = closed v u := by
  have he : (u == v) = (v == u) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨Eq.symm, Eq.symm⟩
  simp only [closed, adjacent_symmetric u v, he]

theorem closed_self {d : Nat} (u : Vertex d) : closed u u = true := by
  simp [closed]

end ExactCubeCodes
