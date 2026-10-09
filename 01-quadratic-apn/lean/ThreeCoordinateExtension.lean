import SevenPointAffineCube

namespace BooleanANF

def dropLast : Block →ₗ[F₂] TripleBlock where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendThreeLinear (L : TripleBlock →ₗ[F₂] Block) (w : Block) : Block →ₗ[F₂] Block :=
  L.comp dropLast + (LinearMap.proj 3).smulRight w

/-- Extend an injective three-dimensional coordinate map to genuine four-dimensional
coordinates. The extra direction is chosen outside its eight-point image. -/
theorem extend_three_coordinates (L : TripleBlock →ₗ[F₂] Block)
    (hinj : Function.Injective L) :
    ∃ e : Block ≃ₗ[F₂] Block, ∀ v : TripleBlock, e ![v 0,v 1,v 2,0] = L v := by
  classical
  have hnot : ¬Function.Surjective L := by
    intro hs
    have hc := Fintype.card_le_of_surjective L hs
    have h3 : Fintype.card TripleBlock = 8 := by decide
    have h4 : Fintype.card Block = 16 := by decide
    rw [h3,h4] at hc
    omega
  obtain ⟨w,hw⟩ : ∃ w, ∀ v, L v ≠ w := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnot
  have hlinj : Function.Injective (extendThreeLinear L w) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change L (dropLast x) + x 3 • w = 0 at hx
    have hbit : x 3 = 0 ∨ x 3 = 1 := by generalize x 3 = z; fin_cases z <;> simp
    rcases hbit with h0 | h1
    · rw [h0, zero_smul, add_zero] at hx
      have hdrop : dropLast x = 0 := hinj (hx.trans (map_zero L).symm)
      funext i
      fin_cases i
      · exact congrFun hdrop 0
      · exact congrFun hdrop 1
      · exact congrFun hdrop 2
      · exact h0
    · rw [h1, one_smul] at hx
      exfalso
      apply hw (dropLast x)
      have he := eq_neg_of_add_eq_zero_left hx
      simpa only [show -w = w by funext i; exact CharTwo.neg_eq (w i)] using he
  let e := LinearEquiv.ofBijective (extendThreeLinear L w)
    ((Finite.injective_iff_surjective).mp hlinj |> fun hs => ⟨hlinj,hs⟩)
  refine ⟨e, ?_⟩
  intro v
  have hdrop : dropLast ![v 0,v 1,v 2,0] = v := by
    funext i
    fin_cases i <;> rfl
  change L (dropLast ![v 0,v 1,v 2,0]) + (0 : F₂) • w = L v
  rw [hdrop, zero_smul, add_zero]

end BooleanANF

namespace BooleanANF

def lastBasis : Block := ![0,0,0,1]

def transvection (φ : Block →ₗ[F₂] F₂) (v : Block) : Block →ₗ[F₂] Block :=
  LinearMap.id + φ.smulRight v

theorem transvection_involutive (φ : Block →ₗ[F₂] F₂) (v : Block) (hv : φ v = 0) :
    Function.Involutive (transvection φ v) := by
  intro x
  change (x + φ x • v) + φ (x + φ x • v) • v = x
  rw [map_add, map_smul, hv]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

/-- Every nonzero direction may be made the last coordinate by an explicit
involutive transvection. No quotient-space choice or rank certificate is assumed. -/
theorem last_coordinate_of_nonzero (r : Block) (hr : r ≠ 0) :
    ∃ e : Block ≃ₗ[F₂] Block, e lastBasis = r := by
  classical
  have hbits : ∀ i, r i = 0 ∨ r i = 1 := by
    intro i
    generalize r i = z
    fin_cases z <;> simp
  have hφ : ∃ φ : Block →ₗ[F₂] F₂, φ r = 1 ∧ φ lastBasis = 1 := by
    rcases hbits 3 with h0 | h1
    · have hex : ∃ i, r i = 1 := by
        apply Classical.byContradiction
        intro hn
        apply hr
        funext i
        exact (hbits i).resolve_right (fun hi => hn ⟨i,hi⟩)
      obtain ⟨i,hi⟩ := hex
      have hi3 : i ≠ 3 := by intro he; subst i; rw [h0] at hi; exact zero_ne_one hi
      refine ⟨(LinearMap.proj 3 : Block →ₗ[F₂] F₂) + LinearMap.proj i, ?_, ?_⟩
      · simp [h0, hi]
      · have hz : lastBasis i = 0 := by
          fin_cases i <;> simp_all [lastBasis]
        change lastBasis 3 + lastBasis i = 1
        rw [hz]
        rfl
    · exact ⟨LinearMap.proj 3, h1, rfl⟩
  obtain ⟨φ,hφr,hφe⟩ := hφ
  have hv : φ (r+lastBasis) = 0 := by rw [map_add,hφr,hφe]; rfl
  let e := LinearEquiv.ofBijective (transvection φ (r+lastBasis))
    (transvection_involutive φ (r+lastBasis) hv).bijective
  refine ⟨e,?_⟩
  change lastBasis + φ lastBasis • (r+lastBasis) = r
  rw [hφe,one_smul]
  funext i
  simp only [Pi.add_apply]
  ring_nf
  simp [CharTwo.two_eq_zero]

end BooleanANF
