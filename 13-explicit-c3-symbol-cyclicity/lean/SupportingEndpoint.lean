module
public import PowerInterface

@[expose] public section
noncomputable section
namespace PrimeFiveFamily
open PrimeCyclicityEndpoint
variable {K A : Type*} [Field K] [CharZero K] [DivisionRing A] [Algebra K A]
variable (s : SymbolFamily K A)

/-- Supporting conditional theorem ONLY. The full N^5 certificate must supply
hpower before this can prove the requested family result. This hypothesis is
visible and is not part of SymbolFamily or claimed established here. -/
theorem supporting_cyclicity_of_fifthPower_identity (a : K)
    (hpower : frozenNumerator s ^ 5 = algebraMap K A a) :
    letI := fixedDivisionRing s
    letI : FiniteDimensional (FixedScalars s) (FixedAlgebra s) :=
      FiniteDimensional.of_finrank_pos (by rw [fixed_finrank]; decide)
    Module.finrank (FixedScalars s)
        (Generated (FixedScalars s) (FixedAlgebra s) (fixedNumerator s)) = 5 ∧
      IsGalois (FixedScalars s)
        (Generated (FixedScalars s) (FixedAlgebra s) (fixedNumerator s)) ∧
      IsCyclic (Gal(Generated (FixedScalars s) (FixedAlgebra s) (fixedNumerator s) /
        FixedScalars s)) ∧
      ∀ M : Subalgebra (FixedScalars s) (FixedAlgebra s),
        Generated (FixedScalars s) (FixedAlgebra s) (fixedNumerator s) ≤ M →
          (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) →
            M = Generated (FixedScalars s) (FixedAlgebra s) (fixedNumerator s) := by
  letI := fixedDivisionRing s
  letI : FiniteDimensional (FixedScalars s) (FixedAlgebra s) :=
    FiniteDimensional.of_finrank_pos (by rw [fixed_finrank]; decide)
  have hc : CenterIsScalars (FixedScalars s) (FixedAlgebra s) := by
    intro d hd
    exact (fixed_center s d).mp hd
  exact abstract_cyclicity_endpoint (FixedScalars s) (FixedAlgebra s)
    (fixed_finrank s) hc (fixedNumerator s) (fixedNumerator_not_scalar s)
    ⟨a, fifthPower_scalar_fixed s a hpower⟩ (fixedNumerator_fifth_of_identity s a hpower)
    (qFixed s) (qFixed_primitive s)

end PrimeFiveFamily
