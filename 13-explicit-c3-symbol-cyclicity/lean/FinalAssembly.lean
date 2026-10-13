module
public import SupportingEndpoint
public import FrozenCentralOutput75
public import modern.N5Fifth

@[expose] public section
noncomputable section
namespace PrimeFiveFamily
open PrimeCyclicityEndpoint
variable {K A : Type*} [Field K] [CharZero K] [DivisionRing A] [Algebra K A]
variable (s : SymbolFamily K A)

/-- Required kernel-checked literal alignment, not an external data comparison. -/
theorem fifthOutput_eq_candidate :
    PrimeCyclicity.N5Modern.acc69 = FrozenCentralOutput75.candidateOutput75 := by
  decide +kernel

def fifthScalar : K := ConcreteCoordinateBridge.centralCoefficient
  s.q s.x s.y FrozenCentralOutput75.candidateOutput75

theorem frozenNumerator_fifth :
    frozenNumerator s ^ 5 = algebraMap K A (fifthScalar s) := by
  calc
    frozenNumerator s ^ 5 = PrimeCyclicity.evalLaurent s.q s.U s.V
        PrimeCyclicity.N5Modern.acc69 := by
      exact PrimeCyclicity.N5Modern.numerator_fifth s.q (scalarQ s) s.U s.V
        (scalarQ_coe s) (scalarQ_fifth s) (q_cyclotomic_fourth s)
        s.q_primitive.pow_eq_one (quantum_units s)
        (scalarQ_commutes_U s) (scalarQ_commutes_V s)
    _ = PrimeCyclicity.evalLaurent s.q s.U s.V
        FrozenCentralOutput75.candidateOutput75 := by rw [fifthOutput_eq_candidate]
    _ = algebraMap K A (fifthScalar s) := by
      exact ConcreteCoordinateBridge.evalLaurent_scalar_of_support
        s.q s.x s.y s.U s.V s.fifth_U s.fifth_V
        FrozenCentralOutput75.candidateOutput75
        FrozenCentralOutput75.candidateOutput75_support

/-- Cyclicity for the explicit relative SymbolFamily, with no extra power hypothesis. -/
theorem symbolFamily_cyclicity :
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
  exact supporting_cyclicity_of_fifthPower_identity s (fifthScalar s)
    (frozenNumerator_fifth s)

end PrimeFiveFamily
