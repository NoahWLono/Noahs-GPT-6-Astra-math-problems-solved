import MatchingPfaffian
set_option maxHeartbeats 500000
namespace MatchingDeterminant
open scoped BigOperators
open Equiv BooleanANF
abbrev Vec8 := Fin 8 → F
abbrev Mat8 := Matrix (Fin 8) (Fin 8) F

/-- Every intrinsic perfect matching of eight coordinates has four edges. -/
theorem matching_card_eight (σ : Perm (Fin 8)) (hσ : σ ∈ matchings) :
    (representatives σ).card = 4 := by
  have hh := (mem_matchings σ).mp hσ
  have hc := twice_card_representatives σ hh.1 hh.2
  simp only [Fintype.card_fin] at hc
  omega

theorem degree_linear_entry (L : Vec8 →ₗ[F] Mat8) (i j : Fin 8) :
    HasDegreeLE (fun b => L b i j) 1 := by
  have h := PfaffianEight.degree_pencil_entry (fun i j k => L (Pi.single k 1) i j) i j
  simpa only [← PfaffianEight.linear_pencil_eq L] using h

theorem degree_matching_root (L : Vec8 →ₗ[F] Mat8)
    (σ : Perm (Fin 8)) (hσ : σ ∈ matchings) :
    HasDegreeLE (fun b => matchingRoot (L b) σ) 4 := by
  have h := HasDegreeLE.prod (representatives σ) (fun i b => L b (σ i) i)
    (fun _ => 1) (fun i _ => degree_linear_entry L (σ i) i)
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, matching_card_eight σ hσ]
    using h

/-- The intrinsic matching Pfaffian on any eight-coordinate linear matrix
pencil has canonical squarefree Boolean ANF degree at most four. -/
theorem degree_pfaffian_linear (L : Vec8 →ₗ[F] Mat8) :
    HasDegreeLE (fun b => pfaffian (L b)) 4 := by
  exact HasDegreeLE.sum matchings (fun σ b => matchingRoot (L b) σ) 4
    (fun σ hσ => degree_matching_root L σ hσ)

theorem pfaffian_one_iff_nondegenerate (M : Mat8)
    (hs : ∀ i j, M i j = M j i) (hd : ∀ i, M i i = 0) :
    pfaffian M = 1 ↔ Matrix.Nondegenerate M := by
  rw [Matrix.nondegenerate_iff_det_ne_zero, det_eq_pfaffian_sq M hs hd,
    PfaffianEight.square_eq_self]
  exact PfaffianEight.one_iff_nonzero _

/-- Actual nonsingularity indicator, equal to one precisely for nondegenerate matrices. -/
abbrev nonsingularIndicator := PfaffianEight.nonsingularIndicator

theorem indicator_eq_pfaffian (M : Mat8)
    (hs : ∀ i j, M i j = M j i) (hd : ∀ i, M i i = 0) :
    nonsingularIndicator M = pfaffian M := by
  change PfaffianEight.nonsingularIndicator M = pfaffian M
  rw [PfaffianEight.indicator_eq_det, det_eq_pfaffian_sq M hs hd,
    PfaffianEight.square_eq_self]

/-- The actual nondegeneracy indicator on an alternating eight-dimensional
binary linear pencil has canonical Boolean ANF degree at most four. -/
theorem degree_nonsingular_indicator (L : Vec8 →ₗ[F] Mat8)
    (hs : ∀ b i j, L b i j = L b j i) (hd : ∀ b i, L b i i = 0) :
    HasDegreeLE (fun b => nonsingularIndicator (L b)) 4 := by
  have heq : (fun b => nonsingularIndicator (L b)) = (fun b => pfaffian (L b)) := by
    funext b
    exact indicator_eq_pfaffian (L b) (hs b) (hd b)
  rw [heq]
  exact degree_pfaffian_linear L

theorem degree_singular_indicator (L : Vec8 →ₗ[F] Mat8)
    (hs : ∀ b i j, L b i j = L b j i) (hd : ∀ b i, L b i i = 0) :
    HasDegreeLE (fun b => 1 + nonsingularIndicator (L b)) 4 := by
  exact ((degree_const 1).mono (by omega)).add (degree_nonsingular_indicator L hs hd)

#print axioms degree_nonsingular_indicator
#print axioms pfaffian_one_iff_nondegenerate
end MatchingDeterminant
