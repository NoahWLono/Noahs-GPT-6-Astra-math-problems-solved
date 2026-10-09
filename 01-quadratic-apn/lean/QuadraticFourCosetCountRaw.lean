import QuadraticFourRadicalRaw
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw

def nonzeroCosets (f g h i j k : F) : Finset (V → F) :=
  (Finset.univ.filter (fun a : V => ¬ inRadical f g h i j k a)).image
    (fun a x => radicalIndicator f g h i j k (x+a))

theorem coset_count000 : ∀ i j k : F, radicalCard 0 0 0 i j k = 4 →
    (nonzeroCosets 0 0 0 i j k).card = 3 := by decide

theorem coset_count001 : ∀ i j k : F, radicalCard 0 0 1 i j k = 4 →
    (nonzeroCosets 0 0 1 i j k).card = 3 := by decide

theorem coset_count010 : ∀ i j k : F, radicalCard 0 1 0 i j k = 4 →
    (nonzeroCosets 0 1 0 i j k).card = 3 := by decide

theorem coset_count011 : ∀ i j k : F, radicalCard 0 1 1 i j k = 4 →
    (nonzeroCosets 0 1 1 i j k).card = 3 := by decide

theorem coset_count100 : ∀ i j k : F, radicalCard 1 0 0 i j k = 4 →
    (nonzeroCosets 1 0 0 i j k).card = 3 := by decide

theorem coset_count101 : ∀ i j k : F, radicalCard 1 0 1 i j k = 4 →
    (nonzeroCosets 1 0 1 i j k).card = 3 := by decide

theorem coset_count110 : ∀ i j k : F, radicalCard 1 1 0 i j k = 4 →
    (nonzeroCosets 1 1 0 i j k).card = 3 := by decide

theorem coset_count111 : ∀ i j k : F, radicalCard 1 1 1 i j k = 4 →
    (nonzeroCosets 1 1 1 i j k).card = 3 := by decide

theorem nonzero_coset_count : ∀ f g h i j k : F, radicalCard f g h i j k = 4 →
    (nonzeroCosets f g h i j k).card = 3 := by
  intro f g h
  fin_cases f <;> fin_cases g <;> fin_cases h
  · exact coset_count000
  · exact coset_count001
  · exact coset_count010
  · exact coset_count011
  · exact coset_count100
  · exact coset_count101
  · exact coset_count110
  · exact coset_count111
end QuadraticFourRaw
