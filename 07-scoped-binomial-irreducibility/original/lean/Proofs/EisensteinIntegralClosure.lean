import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Integer

/-!
A genuine integral-closure wrapper over a DVR. Common denominators are constructed from the
power-basis coordinates, converted to a uniformizer power, and removed by the Eisenstein theorem.
-/
set_option autoImplicit false
open scoped BigOperators nonZeroDivisors
open Algebra Polynomial
namespace PillaiEisenstein
universe u v w
variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Clear the actual finite coordinate denominators of any element of a power-basis field. -/
theorem exists_nonzero_smul_mem_adjoin (B : PowerBasis K L) (z : L) :
    ∃ d : R, d≠0 ∧ d • z∈adjoin R ({B.gen} : Set L) := by
  classical
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun i : Fin B.dim ↦ B.basis.repr z i)
  refine ⟨d,nonZeroDivisors.coe_ne_zero d,?_⟩
  rw [← B.basis.sum_repr z,Finset.smul_sum]
  apply Subalgebra.sum_mem
  intro i _
  obtain ⟨r,hr⟩ := hd i
  rw [← smul_assoc,← hr,algebraMap_smul]
  apply Subalgebra.smul_mem
  rw [B.basis_eq_pow]
  exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _

/-- Over a DVR, the common denominator can be replaced by a power of any uniformizer. -/
theorem exists_uniformizer_pow_smul_mem_adjoin [IsDiscreteValuationRing R]
    (B : PowerBasis K L) (π : R) (hπ : Irreducible π) (z : L) :
    ∃ n : ℕ, π^n • z∈adjoin R ({B.gen} : Set L) := by
  obtain ⟨d,hd,hdz⟩ := exists_nonzero_smul_mem_adjoin (R := R) B z
  obtain ⟨n,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  refine ⟨n,?_⟩
  have hh := (adjoin R ({B.gen} : Set L)).smul_mem hdz (↑(u⁻¹) : R)
  rw [hu,← mul_smul] at hh
  simpa only [← mul_assoc,Units.inv_mul,mul_one,one_mul] using hh

/-- Every integral element of the actual power-basis field belongs to its Eisenstein order. -/
theorem isIntegral_mem_adjoin [IsDiscreteValuationRing R]
    (B : PowerBasis K L) (π : R) (hπ : Irreducible π) (hB : IsIntegral R B.gen)
    (he : (minpoly R B.gen).IsEisensteinAt (Ideal.span {π}))
    (z : L) (hz : IsIntegral R z) : z∈adjoin R ({B.gen} : Set L) := by
  obtain ⟨n,hn⟩ := exists_uniformizer_pow_smul_mem_adjoin B π hπ z
  exact mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    hπ.prime hB hz hn he

/-- Equality with the integral closure, with the denominator condition fully discharged. -/
theorem integralClosure_eq_adjoin [IsDiscreteValuationRing R]
    (B : PowerBasis K L) (π : R) (hπ : Irreducible π) (hB : IsIntegral R B.gen)
    (he : (minpoly R B.gen).IsEisensteinAt (Ideal.span {π})) :
    integralClosure R L=adjoin R ({B.gen} : Set L) := by
  apply le_antisymm
  · intro z hz
    exact isIntegral_mem_adjoin B π hπ hB he z hz
  · exact adjoin_le_integralClosure hB

end PillaiEisenstein
