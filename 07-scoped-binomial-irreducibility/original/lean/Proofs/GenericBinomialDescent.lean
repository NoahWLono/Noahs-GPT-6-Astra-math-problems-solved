import GenericBinomialAffine
import GenericBinomialNewton
import GenericBinomialRamified
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! Generic finite-algebra parameter-prime descent. The actual quotient supplies
its residue, coordinates, conductor, scalar-unit seed, and finite Newton descent;
none of those arithmetic bridges is assumed in the final local/DVR endpoint. -/
set_option autoImplicit false
open Polynomial Algebra
namespace PillaiParameterC
universe u
variable {D : Type u} [CommRing D]

/-- The actual affine equation forces a scalar unit and smaller-order membership.
The local/maximal-ideal condition is explicit, and the Newton scalar-unit seed
is derived rather than assumed. No extension-field or coordinate uniqueness input. -/
theorem local_affine_power_root_descent [IsLocalRing D]
    (ell v : D) {n m r : ℕ}
    (hmax : IsLocalRing.maximalIdeal D = Ideal.span ({ell} : Set D))
    (hv : IsUnit v) (hr : 0 < r) (hrn : r < n) (hnm : n ≤ m)
    (hcop : n.Coprime r) (c : Dˣ) (A : D) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n (c : D) * tau ell v n ^ r)
    (hm : IsUnit (m : D)) :
    IsUnit A ∧ x ∈ Algebra.adjoin D
      ({scalar ell v n (c : D) * tau ell v n ^ r} : Set (Order ell v n)) := by
  have hA := affine_scalar_isUnit ell v hmax hv hr hrn hnm (c : D) A c.isUnit x hx
  obtain ⟨a, ha, hclose⟩ := affine_exists_unit_scalar_seed
    ell v hmax hv hr hrn hnm (c : D) A c.isUnit x hx
  exact ⟨hA, power_root_mem_smaller_order_of_scalar_unit_seed
    ell v n r m hcop c A x hx hm a ha hclose⟩

/-- Natural DVR specialization: irreducibility supplies the maximal-ideal equality.
There is no assumed local degree, maximality, residue compatibility, coordinate
integrality, or pre-existing scalar-unit seed. -/
theorem dvr_affine_power_root_descent [IsDomain D] [IsDiscreteValuationRing D]
    (ell v : D) {n m r : ℕ} (hell : Irreducible ell)
    (hv : IsUnit v) (hr : 0 < r) (hrn : r < n) (hnm : n ≤ m)
    (hcop : n.Coprime r) (c : Dˣ) (A : D) (x : Order ell v n)
    (hx : x ^ m = scalar ell v n A - scalar ell v n (c : D) * tau ell v n ^ r)
    (hm : IsUnit (m : D)) :
    IsUnit A ∧ x ∈ Algebra.adjoin D
      ({scalar ell v n (c : D) * tau ell v n ^ r} : Set (Order ell v n)) :=
  local_affine_power_root_descent ell v hell.maximalIdeal_eq
    hv hr hrn hnm hcop c A x hx hm

end PillaiParameterC
