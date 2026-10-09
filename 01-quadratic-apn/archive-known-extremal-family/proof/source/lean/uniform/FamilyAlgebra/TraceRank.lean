import FamilyAlgebra.FiniteRealization
import Mathlib.LinearAlgebra.BilinearForm.Hom

namespace FamilyAlgebra.TraceRank
variable {F E V : Type*} [Field F] [Field E] [Algebra F E]
  [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]

/-- Scalar transfer of an E-bilinear form through any nonzero F-linear
functional has exactly the original radical, with scalars restricted to F. -/
theorem transfer_ker (T : E →ₗ[F] F) (nonzero : T ≠ 0)
    (B : LinearMap.BilinForm E V) :
    LinearMap.ker (T.compBilinForm B) = (LinearMap.ker B).restrictScalars F := by
  have ht : T.toAddMonoidHom ≠ 0 := by
    intro h
    apply nonzero
    ext x
    exact congrArg (fun f : E →+ F => f x) h
  ext x
  change (T.compBilinForm B) x = 0 ↔ B x=0
  constructor
  · intro h
    ext y
    apply TraceCoordinates.separating T.toAddMonoidHom ht
    intro b
    have hy := congrArg (fun f : V →ₗ[F] F => f (b • y)) h
    change T (B x (b • y))=0 at hy
    rw [map_smul, smul_eq_mul, mul_comm] at hy
    exact hy
  · intro h
    ext y
    change T (B x y)=0
    rw [h]
    simp

/-- Rank is multiplied by the extension degree under nonzero scalar transfer.
Rank here is precisely the dimension of the bilinear form's linear-map range. -/
theorem transfer_rank [FiniteDimensional F E] [FiniteDimensional E V]
    [FiniteDimensional F V]
    (T : E →ₗ[F] F) (nonzero : T ≠ 0) (B : LinearMap.BilinForm E V) :
    Module.finrank F (LinearMap.range (T.compBilinForm B)) =
      Module.finrank F E * Module.finrank E (LinearMap.range B) := by
  have hk : Module.finrank F (LinearMap.ker (T.compBilinForm B)) =
      Module.finrank F E * Module.finrank E (LinearMap.ker B) := by
    rw [transfer_ker T nonzero B]
    change Module.finrank F (LinearMap.ker B) = _
    exact (Module.finrank_mul_finrank F E (LinearMap.ker B)).symm
  have hv := Module.finrank_mul_finrank F E V
  have hf := (T.compBilinForm B).finrank_range_add_finrank_ker
  have he := congrArg (fun d => Module.finrank F E * d) B.finrank_range_add_finrank_ker
  dsimp only at he
  rw [Nat.mul_add] at he
  rw [hk, ← hv] at hf
  omega

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Actual finite-field trace rank multiplication, valid for every positive
degree, including even degree. -/
theorem realized_trace_rank (n : Nat) (positive : 0<n)
    (B : LinearMap.BilinForm (GaloisField 2 n) (Fin 4 → GaloisField 2 n)) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((Algebra.trace (ZMod 2) (GaloisField 2 n)).compBilinForm B)) =
        n * Module.finrank (GaloisField 2 n) (LinearMap.range B) := by
  rw [transfer_rank _ (Algebra.trace_ne_zero (ZMod 2) (GaloisField 2 n)) B,
    GaloisField.finrank 2 (by omega)]

#print axioms transfer_rank
#print axioms realized_trace_rank
end FamilyAlgebra.TraceRank
