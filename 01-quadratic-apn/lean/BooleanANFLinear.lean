import BooleanANF
import Mathlib.LinearAlgebra.Pi

namespace BooleanANF
open scoped BigOperators
variable {ι κ : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ]

/-- Every abstract linear functional has canonical Boolean degree at most one. -/
theorem degree_linear (L : (ι → F₂) →ₗ[F₂] F₂) : HasDegreeLE L 1 := by
  have hx (x : ι → F₂) : x = ∑ i : ι, x i • (Pi.single i 1 : ι → F₂) := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have hrepr : (L : (ι → F₂) → F₂) =
      fun x => ∑ i : ι, L (Pi.single i 1) * x i := by
    funext x
    conv_lhs => rw [hx x, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hrepr]
  apply HasDegreeLE.sum
  intro i hi
  exact (degree_coordinate i).smul _

/-- Actual linear maps can be used directly in the affine substitution theorem. -/
theorem HasDegreeLE.comp_linear {f : (ι → F₂) → F₂} {d : ℕ}
    (hf : HasDegreeLE f d) (L : (κ → F₂) →ₗ[F₂] (ι → F₂)) :
    HasDegreeLE (fun x => f (L x)) d := by
  apply hf.comp_affine L
  intro i
  exact degree_linear ((LinearMap.proj i).comp L)

/-- Translation composed with an actual linear map preserves algebraic degree. -/
theorem HasDegreeLE.comp_linear_translate {f : (ι → F₂) → F₂} {d : ℕ}
    (hf : HasDegreeLE f d) (L : (κ → F₂) →ₗ[F₂] (ι → F₂)) (p : ι → F₂) :
    HasDegreeLE (fun x => f (p + L x)) d := by
  apply hf.comp_affine (fun x => p + L x)
  intro i
  exact ((degree_const (p i)).mono (by decide)).add
    (degree_linear ((LinearMap.proj i).comp L))

end BooleanANF
