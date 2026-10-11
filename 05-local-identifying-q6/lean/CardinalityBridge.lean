import LocalIdentifyingQ6
import CardinalityEncoding

namespace LocalIdentifyingQ6.CardinalityEncoding

theorem prefixCount_eq_finRange (X : Nat → Bool) (n : Nat) :
    prefixCount X n = (List.finRange n).countP (fun v => X (v.val + 1)) := by
  induction n with
  | zero => simp [prefixCount]
  | succ n ih =>
    simp only [prefixCount, List.finRange_succ_last, List.countP_append, List.countP_map,
      List.countP_cons, List.countP_nil, Fin.val_last]
    simp only [Function.comp_def, Fin.coe_castSucc] 
    rw [← ih]
    simp

theorem prefixCount_eq_cardinality (C : Code) (X : Nat → Bool)
    (h : ∀ v : Vertex, X (v.val + 1) = C v) :
    prefixCount X 64 = cardinality C := by
  rw [prefixCount_eq_finRange]
  have he : (fun v : Vertex => X (v.val + 1)) = C := funext h
  rw [he, List.countP_eq_length_filter]
  rfl

#print axioms prefixCount_eq_cardinality
end LocalIdentifyingQ6.CardinalityEncoding
