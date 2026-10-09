import CodeBasis
import QuadraticFourAffineDifference

namespace BooleanANF
open scoped BigOperators

/-- Code coordinates are themselves quadratic words. -/
theorem codeBasisWord_degree {q : DoubleBlock → F₂} {d : ℕ}
    (hq : HasDegreeLE q 4)
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (i : Fin d) :
    HasDegreeLE (codeBasisWord e i) 2 :=
  quadraticCoefficientSpace_degree hq (e (Pi.single i 1)).property

/-- A basis detects exactly the rows where the quadratic part is nonzero. -/
theorem codeBasisWord_detects_rows {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y : Block) :
    y ∈ coefficientRows q ↔ ∃ i, codeBasisWord e i y ≠ 0 := by
  constructor
  · intro hy
    obtain ⟨s,hs⟩ := (Finset.mem_filter.mp hy).2
    by_contra hn
    have hz : ∀ i, codeBasisWord e i y = 0 := by simpa using hn
    apply hs
    rw [coefficient_code_expansion e]
    simp [hz]
  · rintro ⟨i,hi⟩
    by_contra hn
    exact hi (quadraticCoefficientSpace_supported_coefficients q
      (e (Pi.single i 1)).property y hn)

theorem quadraticBasisPart_degree {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (i : Fin d) :
    HasDegreeLE (quadraticBasisPart e i) 2 := by
  apply HasDegreeLE.sum
  intro s hs
  exact ((degree_monomial s.val).mono (by omega)).smul _

theorem quadraticPart_degree (q : DoubleBlock → F₂) (y : Block) :
    HasDegreeLE (quadraticPart q y) 2 := by
  apply HasDegreeLE.sum
  intro s hs
  exact ((degree_monomial s.val).mono (by omega)).smul _

theorem coefficient_quadraticPart (q : DoubleBlock → F₂) (y : Block) (s : QuadraticIndex) :
    coefficient (quadraticPart q y) s.val = fiberCoefficient q s.val y := by
  classical
  unfold quadraticPart
  rw [coefficient_sum]
  simp_rw [coefficient_smul, coefficient_monomial]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t ht hts
    have hval : s.val ≠ t.val := fun h => hts (Subtype.ext h.symm)
    simp [hval]
  · simp

/-- Removing the canonical homogeneous quadratic part leaves an affine row. -/
theorem row_quadraticPart_affine (q : DoubleBlock → F₂) (y : Block)
    (hr : HasDegreeLE (fiber q y) 2) :
    HasDegreeLE (fun x => fiber q y x + quadraticPart q y x) 1 := by
  intro s hs
  rw [coefficient_add]
  by_cases hc : s.card = 2
  · rw [show coefficient (quadraticPart q y) s = fiberCoefficient q s y from
      coefficient_quadraticPart q y ⟨s,hc⟩]
    exact CharTwo.add_self_eq_zero _
  · rw [hr s (by omega), quadraticPart_degree q y s (by omega), zero_add]

theorem zero_polar_of_affine {r : Block → F₂} (hr : HasDegreeLE r 1) (x y : Block) :
    QuadraticFour.polar r x y = 0 := by
  calc
    QuadraticFour.polar r x y = (r (x+y) + r 0) + (r x + r y) := by
      unfold QuadraticFour.polar
      ring
    _ = (r x+r y)+(r x+r y) := by rw [hr.affine_add]
    _ = 0 := CharTwo.add_self_eq_zero _

/-- Polar geometry depends only on the actual quadratic coefficient code part. -/
theorem quadraticPart_polar (q : DoubleBlock → F₂) (y : Block)
    (hr : HasDegreeLE (fiber q y) 2) (x z : Block) :
    QuadraticFour.polar (fiber q y) x z = QuadraticFour.polar (quadraticPart q y) x z := by
  have hh := zero_polar_of_affine (row_quadraticPart_affine q y hr) x z
  rw [QuadraticFour.polar_add] at hh
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh

/-- Homogeneous quadratics have no constant or linear canonical coefficients. -/
theorem quadraticBasisPart_low_coefficient {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (i : Fin d)
    (s : Finset (Fin 4)) (hs : s.card < 2) : coefficient (quadraticBasisPart e i) s = 0 := by
  unfold quadraticBasisPart
  rw [coefficient_sum]
  apply Finset.sum_eq_zero
  intro t ht
  rw [coefficient_smul, coefficient_monomial, if_neg, mul_zero]
  intro he
  have hc := t.property
  rw [← he] at hc
  omega

theorem homogeneous_combination_affine_eq_zero {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (u : Fin d → F₂)
    (ha : HasDegreeLE (fun x => ∑ i : Fin d, u i * quadraticBasisPart e i x) 1) :
    (fun x => ∑ i : Fin d, u i * quadraticBasisPart e i x) = 0 := by
  apply coefficient_injective
  funext s
  have hzero : coefficient (0 : Block → F₂) s = 0 := by simp [coefficient,transform]
  rw [hzero]
  by_cases hs : s.card < 2
  · rw [coefficient_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [coefficient_smul, quadraticBasisPart_low_coefficient e i s hs, mul_zero]
  · exact ha s (by omega)

/-- No nonzero code combination has zero polar; hence the resulting pencil is independent. -/
theorem quadraticBasis_combination_polar_nonzero {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) {u : Fin d → F₂}
    (hu : u ≠ 0) :
    ¬ ∀ x y, QuadraticFour.polar (fun z => ∑ i : Fin d, u i * quadraticBasisPart e i z) x y = 0 := by
  intro hz
  have hd : HasDegreeLE (fun z => ∑ i : Fin d, u i * quadraticBasisPart e i z) 2 := by
    apply HasDegreeLE.sum
    intro i hi
    exact (quadraticBasisPart_degree e i).smul _
  have ha := QuadraticFour.degree_one_of_zero_polar hd hz
  exact quadraticBasis_combination_ne_zero e hu (homogeneous_combination_affine_eq_zero e u ha)

end BooleanANF
