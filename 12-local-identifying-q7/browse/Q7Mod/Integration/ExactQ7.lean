module

public import Q7Mod.Integration.Q7ConditionalOptimum
import Q7Mod.Integration.FiniteBergeCover

public section
namespace Q7GlobalAssembly

theorem localIdentifying_at_least_24
    (C : ExactCubeCodes.Code 7) (hLocal : ExactCubeCodes.LocalIdentifying C) :
    24 ≤ ExactCubeCodes.cardinality C :=
  localIdentifying_at_least_24_of_finite_cover finite_berge8_perfect_cover C hLocal

end Q7GlobalAssembly
namespace ExactCubeCodes

/-- The original local-identifying-code predicate on Q7 has exact minimum 24. -/
theorem localIdentifying_Q7_optimum24 :
    (∃ C : Code 7, LocalIdentifying C ∧ cardinality C = 24) ∧
    (∀ C : Code 7, LocalIdentifying C → 24 ≤ cardinality C) :=
  localIdentifying_Q7_optimum24_of_finite_cover
    Q7GlobalAssembly.finite_berge8_perfect_cover

#print axioms localIdentifying_Q7_optimum24
end ExactCubeCodes
