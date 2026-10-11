import PathNormalization
import CubePathAutomorphism

namespace LocalIdentifyingQ6

/-- Every putative code of size at most 13 can be normalized to contain 0, 1, and 2. -/
theorem normalize_small_code_path (C : Code) (hc : LocalIdentifying C)
    (hcard : cardinality C ≤ 13) :
    ∃ D : Code, LocalIdentifying D ∧ D 0 = true ∧ D 1 = true ∧ D 2 = true ∧
      cardinality D = cardinality C := by
  obtain ⟨c, a, b, hcc, ha, hb, hca, hcb, hab⟩ := small_code_has_path C hc hcard
  exact normalize_code_path C hc c a b hcc ha hb hca hcb hab

#print axioms normalize_small_code_path
end LocalIdentifyingQ6
