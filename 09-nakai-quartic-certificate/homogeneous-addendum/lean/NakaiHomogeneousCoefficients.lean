import NakaiVariableSyzygy
import Mathlib.RingTheory.Ideal.Operations

/-! Homogeneous extraction of polynomial ideal-membership coefficients. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneousCoefficients
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev P := MvPolynomial ι k

/-- A homogeneous right factor shifts the component degree, provided the
requested degree is at least its degree. -/
theorem homogeneousComponent_mul (b g : P (k := k) (ι := ι)) (r N : ℕ)
    (hg : g.IsHomogeneous r) (hr : r ≤ N) :
    homogeneousComponent N (b*g) = homogeneousComponent (N-r) b * g := by
  induction b using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [homogeneousComponent_of_mem ((isHomogeneous_monomial c rfl).mul hg),
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    by_cases he : N-r = d.degree
    · have he' : N = d.degree+r := (Nat.sub_eq_iff_eq_add hr).mp he
      simp [he, he']
    · have he' : N ≠ d.degree+r := fun hh => he ((Nat.sub_eq_iff_eq_add hr).mpr hh)
      simp [he, he']
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]

/-- Pure-power membership admits coefficients of the unique compatible degree. -/
theorem homogeneous_pure_power_coefficients (g : ι → P (k := k) (ι := ι)) (r N : ℕ)
    (hg : ∀ j, (g j).IsHomogeneous r) (hr : r ≤ N)
    (hpowers : ∀ i : ι, (X i : P (k := k) (ι := ι))^N ∈ Ideal.span (Set.range g)) :
    ∃ B : Matrix ι ι (P (k := k) (ι := ι)),
      (∀ i j, (B i j).IsHomogeneous (N-r)) ∧
      (∀ i, ∑ j, B i j * g j = (X i)^N) := by
  choose B hB using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hpowers i)
  refine ⟨fun i j => homogeneousComponent (N-r) (B i j), ?_, ?_⟩
  · intro i j
    exact homogeneousComponent_isHomogeneous _ _
  · intro i
    have hh := congrArg (homogeneousComponent N) (hB i)
    rw [map_sum] at hh
    have hX : ((X i : P (k := k) (ι := ι))^N).IsHomogeneous N := by
      simpa using (isHomogeneous_X k i).pow N
    rw [homogeneousComponent_eq_self hX] at hh
    simpa only [homogeneousComponent_mul _ _ r N (hg _) hr] using hh

#print axioms homogeneousComponent_mul
#print axioms homogeneous_pure_power_coefficients
end NakaiHomogeneousCoefficients
