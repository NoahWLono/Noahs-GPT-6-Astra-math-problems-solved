import WeightThirtyRankThreePencil

namespace BooleanANF

private theorem firstThreeZero_iff_drop (x : Block) : firstThreeZero x ↔ dropLast x = 0 := by
  constructor
  · intro h
    funext i
    fin_cases i <;> exact h _ (by decide)
  · intro h i hi
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
    · exact False.elim (hi rfl)

private theorem firstThreeEq_iff_drop (x y : Block) :
    (∀ i : Fin 4, i ≠ 3 → x i = y i) ↔ dropLast x = dropLast y := by
  constructor
  · intro h
    funext i
    fin_cases i <;> exact h _ (by decide)
  · intro h i hi
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
    · exact False.elim (hi rfl)

private theorem block_of_last_zero (y : Block) (hy : y 3 = 0) :
    y = ![dropLast y 0, dropLast y 1, dropLast y 2, 0] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hy

/-- The specialized dimension-three classification, with genuine affine transport
and an explicit pair of transverse four-flats. -/
theorem weight_thirty_case_three {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    TwoTransverseFlats (residualSignal q) := by
  obtain ⟨e,p,L,ex,R,hL,hcoord,hshape⟩ := h.three_pencil_coordinates hd
  have hsize : (coefficientRows q).card = 7 :=
    (coefficientSpace_dimension_three h.totalDegree h.activeBound hd).1
  have hzero (y : Block) (hy : codeEvaluation e y = 0) : fiber q y = 0 := by
    apply normalized_no_extra_affine h (by omega) y
    intro hm
    exact ((codeEvaluation_nonzero_iff e y).mpr hm) hy
  have hpzero : fiber q p = 0 :=
    hzero p (code_affine_missing_point e p L hL hcoord)
  obtain ⟨ey,hey⟩ := extend_three_coordinates (L.comp R.symm.toLinearMap)
    (hL.comp R.symm.injective)
  have hey' (v : SimplexIndex) : ey ![v 0,v 1,v 2,0] = L (R.symm v) := hey v
  apply typeB_of_coordinates q p ex ey
  intro x y
  change fiber q (p + ey y) (ex x) = typeBResidual (Sum.elim x y)
  by_cases hy3 : y 3 = 0
  · have heyval : ey y = L (R.symm (dropLast y)) := by
      conv_lhs => rw [block_of_last_zero y hy3]
      exact hey' _
    rw [heyval]
    by_cases hy0 : dropLast y = 0
    · rw [hy0, map_zero, map_zero, add_zero]
      rw [hpzero]
      simp [typeBResidual, firstThreeZero_iff_drop, hy0]
    · have hv : R.symm (dropLast y) ≠ 0 := by
        intro hz
        apply hy0
        have hh := congrArg R hz
        simpa using hh
      rw [hshape _ hv, R.apply_symm_apply]
      simp only [typeBResidual, Sum.elim_inl, Sum.elim_inr]
      simp only [firstThreeZero_iff_drop, firstThreeEq_iff_drop, hy3, hy0,
        not_false_eq_true, true_and]
  · have hcol : codeEvaluation e (p+ey y) = 0 := by
      by_cases hz : codeEvaluation e (p+ey y) = 0
      · exact hz
      have hc := (hcoord _ hz (p+ey y)).mp rfl
      have he : ey y = L (codeEvaluation e (p+ey y)) := add_left_cancel hc
      have he' : ey y = ey ![(R (codeEvaluation e (p+ey y))) 0,
          (R (codeEvaluation e (p+ey y))) 1, (R (codeEvaluation e (p+ey y))) 2,0] := by
        rw [hey', R.symm_apply_apply]
        exact he
      have heq := ey.injective he'
      have hh := congrFun heq 3
      exact False.elim (hy3 hh)
    rw [hzero _ hcol]
    simp [typeBResidual,hy3]

#print axioms weight_thirty_case_three
end BooleanANF
