import MatchingDeterminant
set_option maxHeartbeats 500000
namespace MatchingDeterminant
open scoped BigOperators
open Equiv
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

def representatives (σ : Perm ι) : Finset ι := Finset.univ.filter (fun i => i < σ i)

theorem mate_mate (σ : Perm ι) (h : σ⁻¹ = σ) (i : ι) : σ (σ i) = i := by
  calc
    σ (σ i) = σ⁻¹ (σ i) := congrArg (fun f : Perm ι => f (σ i)) h.symm
    _ = i := σ.inv_apply_self i

theorem representatives_image (σ : Perm ι) (h : σ⁻¹ = σ) (hf : ∀ i, σ i ≠ i) :
    (representatives σ).image σ = Finset.univ.filter (fun i => ¬ i < σ i) := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have ha' : a < σ a := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mate_mate σ h]
    exact not_lt_of_ge ha'.le
  · intro hb
    have hb' : ¬ b < σ b := (Finset.mem_filter.mp hb).2
    have hl : σ b < b := by
      rcases lt_trichotomy b (σ b) with hlt | heq | hlt
      · exact False.elim (hb' hlt)
      · exact False.elim (hf b heq.symm)
      · exact hlt
    apply Finset.mem_image.mpr
    refine ⟨σ b, ?_, mate_mate σ h b⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rwa [mate_mate σ h]

theorem twice_card_representatives (σ : Perm ι) (h : σ⁻¹ = σ) (hf : ∀ i, σ i ≠ i) :
    2 * (representatives σ).card = Fintype.card ι := by
  have hc : (Finset.univ.filter (fun i => ¬ i < σ i)).card = (representatives σ).card := by
    rw [← representatives_image σ h hf]
    exact Finset.card_image_of_injective _ σ.injective
  have hh : (representatives σ).card +
      (Finset.univ.filter (fun i => ¬ i < σ i)).card = Fintype.card ι := by
    simpa [representatives] using Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => i < σ i) (f := fun _ => (1 : ℕ))
  rw [hc] at hh
  omega

def matchingRoot (M : Matrix ι ι F) (σ : Perm ι) : F :=
  ∏ i ∈ representatives σ, M (σ i) i

theorem weight_eq_root_sq (M : Matrix ι ι F) (hs : ∀ i j, M i j = M j i)
    (σ : Perm ι) (h : σ⁻¹ = σ) (hf : ∀ i, σ i ≠ i) :
    weight M σ = (matchingRoot M σ) ^ 2 := by
  have hp : (∏ i ∈ Finset.univ.filter (fun i => ¬ i < σ i), M (σ i) i) =
      matchingRoot M σ := by
    rw [← representatives_image σ h hf,
      Finset.prod_image (fun a _ b _ hab => σ.injective hab)]
    apply Finset.prod_congr rfl
    intro i _
    rw [mate_mate σ h]
    exact hs i (σ i)
  have hh := Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => i < σ i) (f := fun i => M (σ i) i)
  rw [hp] at hh
  exact hh.symm.trans (pow_two _).symm

/-- Intrinsic matching Pfaffian. Each fixed-point-free involution is exactly
one perfect matching; the smaller endpoint represents each two-element orbit. -/
def pfaffian (M : Matrix ι ι F) : F := ∑ σ ∈ matchings, matchingRoot M σ

theorem det_eq_pfaffian_sq (M : Matrix ι ι F)
    (hs : ∀ i j, M i j = M j i) (hd : ∀ i, M i i = 0) :
    M.det = (pfaffian M) ^ 2 := by
  rw [det_eq_matchings M hs hd, pfaffian, CharTwo.sum_sq]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hh := Finset.mem_filter.mp hσ
  exact weight_eq_root_sq M hs σ (Finset.mem_filter.mp hh.1).2 hh.2

#print axioms det_eq_pfaffian_sq
#print axioms twice_card_representatives
end MatchingDeterminant
