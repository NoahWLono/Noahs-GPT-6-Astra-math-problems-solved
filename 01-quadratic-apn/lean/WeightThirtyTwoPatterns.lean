import CodeBasisProperties
import CoefficientPatterns
import NormalizedCostBudget

set_option maxHeartbeats 1600000
namespace BooleanANF
open scoped BigOperators
open QuadraticFour

theorem pair_pattern_sum (a b : Block → F₂) (R : F₂ → F₂ → F₂) :
    (∑ y, R (a y) (b y)) = pairPatternCount a b 0 0 • R 0 0 +
      pairPatternCount a b 1 0 • R 1 0 + pairPatternCount a b 0 1 • R 0 1 +
      pairPatternCount a b 1 1 • R 1 1 := by
  simp only [pairPatternCount, ← Finset.sum_nsmul_assoc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  generalize a y = u
  generalize b y = v
  fin_cases u <;> fin_cases v <;> simp

theorem rank_two_row_polar {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y x z : Block) :
    polar (fiber q y) x z = polar (fun t => codeBasisWord e 0 y * quadraticBasisPart e 0 t +
      codeBasisWord e 1 y * quadraticBasisPart e 1 t) x z := by
  rw [quadraticPart_polar q y (h.rowDegree y)]
  have he : quadraticPart q y = fun t => codeBasisWord e 0 y * quadraticBasisPart e 0 t +
      codeBasisWord e 1 y * quadraticBasisPart e 1 t := by
    funext t
    rw [quadraticPart_code_expansion e]
    simp [Fin.sum_univ_two]
  rw [he]

theorem rank_two_coefficient_rows {q : DoubleBlock → F₂}
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y : Block) :
    y ∈ coefficientRows q ↔ codeBasisWord e 0 y ≠ 0 ∨ codeBasisWord e 1 y ≠ 0 := by
  rw [codeBasisWord_detects_rows e]
  simp [Fin.exists_fin_two]

theorem rank_two_pattern_total {q : DoubleBlock → F₂}
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) :
    pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 0 +
      pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 0 1 +
      pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 1 =
      (coefficientRows q).card := by
  rw [pair_pattern_total]
  congr 1
  ext y
  simp [rank_two_coefficient_rows e]

end BooleanANF
