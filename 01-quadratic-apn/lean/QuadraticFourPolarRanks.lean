import QuadraticFourAffineDifference

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace BooleanANF.QuadraticFour

private theorem raw_radical_cards : ∀ f g h i j k : F₂,
    QuadraticFourRaw.radicalCard f g h i j k ∈ ({1,4,16} : Finset ℕ) := by decide

theorem quadratic_radical_cards {q : V → F₂} (hq : HasDegreeLE q 2) :
    (radicalPoints q).card ∈ ({1,4,16} : Finset ℕ) := by
  apply quadratic_induction hq
  intro a b c d e f g h i j k
  rw [radicalCard_poly]
  exact raw_radical_cards f g h i j k

theorem radical_sixteen_affine {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 16) : HasDegreeLE q 1 := by
  apply degree_one_of_zero_polar hq
  have he : radicalPoints q = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [V, Fintype.card_fun, ZMod.card] using hr
  intro x y
  have hx : x ∈ radicalPoints q := by rw [he]; exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hx).2 y

theorem nonaffine_radical_cards {q : V → F₂} (hq : HasDegreeLE q 2)
    (ha : ¬ HasDegreeLE q 1) : (radicalPoints q).card = 1 ∨ (radicalPoints q).card = 4 := by
  have h := quadratic_radical_cards hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (ha (radical_sixteen_affine hq h)).elim

#print axioms nonaffine_radical_cards
end BooleanANF.QuadraticFour
