import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.FieldTheory.Minpoly.Field

/-!
Reduced coordinates recovered from actual smaller-order membership and a derived
minimal-polynomial degree. The concrete application establishes both inputs.
-/
set_option autoImplicit false
open Algebra Polynomial
namespace PillaiParameterCoordinates
universe u v w
variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [Field K] [Field L]
variable [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Actual smaller-order membership recovers reduced integral coordinates.
No claim that the polynomial f is Eisenstein is made or needed here. -/
theorem reduced_polynomial_lift_of_adjoin
    (t : L) (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hroot : aeval t f = 0)
    (hminDeg : (minpoly K t).natDegree = f.natDegree)
    (G : K[X]) (hG : G.natDegree < f.natDegree)
    (hmem : aeval t G ∈ adjoin R ({t} : Set L)) :
    ∃ H : R[X], H.natDegree < f.natDegree ∧ H.map (algebraMap R K) = G := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  let H : R[X] := Q %ₘ f
  have hfOne : f ≠ 1 := by
    intro h
    simp only [h, natDegree_one, lt_self_iff_false] at hdeg
  have hH : H.natDegree < f.natDegree :=
    natDegree_modByMonic_lt Q hf hfOne
  have hHeval : aeval t H = aeval t G := by
    change aeval t (Q %ₘ f) = aeval t G
    rw [aeval_modByMonic_eq_self_of_root hroot]
    exact hQ
  have hzero : aeval t (H.map (algebraMap R K) - G) = 0 := by
    rw [map_sub, aeval_map_algebraMap, hHeval, sub_self]
  have hdvd : minpoly K t ∣ H.map (algebraMap R K) - G :=
    minpoly.dvd K t hzero
  have hmapDeg : (H.map (algebraMap R K)).natDegree < f.natDegree :=
    lt_of_le_of_lt natDegree_map_le hH
  have hdiffDeg : (H.map (algebraMap R K) - G).natDegree <
      (minpoly K t).natDegree := by
    rw [hminDeg]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hmapDeg hG)
  refine ⟨H, hH, ?_⟩
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdvd hdiffDeg)

end PillaiParameterCoordinates
