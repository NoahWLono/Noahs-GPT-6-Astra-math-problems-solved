import WeightThirtyCaseZero
import WeightThirtyCaseOne
import WeightThirtyCaseTwo
import WeightThirtyRankThreeFinal
import WeightThirtySupportProfile

/-! Specialized, self-contained RM(4,8) weight-thirty classification.
No general Kasami–Tokura classification theorem is imported or assumed. -/
namespace BooleanANF

/-- All four possible dimensions of the actual coefficient code are exhausted. -/
theorem normalized_quartic_two_flats (q : DoubleBlock → F₂) (h : NormalizedQuartic q) :
    TwoTransverseFlats (residualSignal q) := by
  have hb := h.code_dimension
  have hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 0 ∨
      Module.finrank F₂ (quadraticCoefficientSpace q) = 1 ∨
      Module.finrank F₂ (quadraticCoefficientSpace q) = 2 ∨
      Module.finrank F₂ (quadraticCoefficientSpace q) = 3 := by omega
  rcases hd with hd | hd | hd | hd
  · exact weight_thirty_case_zero_finrank h hd
  · exact weight_thirty_case_one h hd
  · exact False.elim (weight_thirty_case_two h hd)
  · exact weight_thirty_case_three h hd

/-- Every actual degree-four Boolean function on eight variables of weight thirty is
exactly the symmetric-difference indicator of two transverse affine four-flats. -/
theorem quartic_weight_thirty_two_flats (f : EightSpace → F₂)
    (hf : HasDegreeLE f 4) (hw : weight f = 30) : TwoTransverseFlats f :=
  transfer_normalized_classification normalized_quartic_two_flats f hf hw

/-- The linear-coordinate support profile needed for the APN application. -/
theorem quartic_weight_thirty_nonzero_support_profile (f : EightSpace → F₂)
    (hf : HasDegreeLE f 4) (hw : weight f = 30) (hzero : f 0=1) :
    ∃ (e : (Block × Block) ≃ₗ[F₂] EightSpace) (c : Block), c≠0 ∧
      ∀ a v : Block,
        (f (e (a,v))=1 ∧ e (a,v)≠0) ↔
          (v=0 ∧ a≠0 ∧ a≠c) ∨ (a=c ∧ v≠0) :=
  TwoTransverseFlats.nonzero_support_profile f (quartic_weight_thirty_two_flats f hf hw) hzero

#print axioms normalized_quartic_two_flats
#print axioms quartic_weight_thirty_two_flats
#print axioms quartic_weight_thirty_nonzero_support_profile

end BooleanANF
