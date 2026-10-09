import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Field.ZMod
import SingletonFiberCount
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Free

namespace BooleanANF
open scoped BigOperators
open Module
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev EightSpace := Fin 8 → F₂

/-- A linear subspace meeting a translated support only at zero. -/
def AvoidsNonzero (S : Finset EightSpace) (W : Submodule F₂ EightSpace) : Prop :=
  ∀ x ∈ S, x ∈ W → x = 0

private theorem eight_card : Fintype.card EightSpace = 256 := by
  simp [EightSpace, Fintype.card_fun, ZMod.card]

private theorem subspace_card (W : Submodule F₂ EightSpace) :
    Nat.card W = 2 ^ finrank F₂ W := by
  classical
  letI := Fintype.ofFinite W
  simpa [Nat.card_eq_fintype_card, ZMod.card] using (Module.card_eq_pow_finrank (K := F₂) (V := W))

/-- The greedy extension counting step uses at most |S| |W| blocked vectors. -/
theorem exists_unblocked_vector (S : Finset EightSpace) (W : Submodule F₂ EightSpace)
    (hsize : S.card * 2 ^ finrank F₂ W < 256) :
    ∃ v : EightSpace, ∀ s ∈ S, ∀ w ∈ W, v ≠ s + w := by
  classical
  let B := (S ×ˢ (W : Set EightSpace).toFinset).image (fun p => p.1 + p.2)
  have hcard : B.card < (Finset.univ : Finset EightSpace).card := by
    calc
      B.card ≤ (S ×ˢ (W : Set EightSpace).toFinset).card := Finset.card_image_le
      _ = S.card * Nat.card W := by
        rw [Finset.card_product, Set.toFinset_card]
        congr 1
        exact (Nat.card_eq_fintype_card).symm
      _ = S.card * 2 ^ finrank F₂ W := by rw [subspace_card]
      _ < 256 := hsize
      _ = (Finset.univ : Finset EightSpace).card := by simp [eight_card]
  obtain ⟨v, hv, hnv⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  refine ⟨v, ?_⟩
  intro s hs w hw he
  apply hnv
  exact Finset.mem_image.mpr ⟨(s,w), Finset.mem_product.mpr ⟨hs, by simpa using hw⟩, he.symm⟩

/-- One new direction doubles the avoiding subspace while retaining singleton intersection. -/
theorem extend_avoiding_subspace (S : Finset EightSpace) (hzero : 0 ∈ S)
    (W : Submodule F₂ EightSpace) (hW : AvoidsNonzero S W)
    (hsize : S.card * 2 ^ finrank F₂ W < 256) :
    ∃ W' : Submodule F₂ EightSpace,
      finrank F₂ W' = finrank F₂ W + 1 ∧ AvoidsNonzero S W' := by
  classical
  obtain ⟨v, hv⟩ := exists_unblocked_vector S W hsize
  have hvW : v ∉ W := by
    intro h
    exact hv 0 hzero v h (zero_add v).symm
  have hv0 : v ≠ 0 := by
    intro h
    exact hvW (h ▸ W.zero_mem)
  refine ⟨W ⊔ Submodule.span F₂ {v}, ?_, ?_⟩
  · have hd := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F₂ {v})
    have hj : Disjoint W (Submodule.span F₂ {v}) := Submodule.disjoint_span_singleton_of_not_mem hvW
    rw [hj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv0] at hd
    exact hd
  · intro x hx hxW
    rcases Submodule.mem_sup.mp hxW with ⟨w, hw, z, hz, hwz⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases ha with rfl | rfl
    · simp only [zero_smul, add_zero] at hwz
      exact hW x hx (hwz ▸ hw)
    · simp only [one_smul] at hwz
      have hw2 : w + w = 0 := by funext i; exact CharTwo.add_self_eq_zero (w i)
      have he : v = x + w := by
        rw [← hwz]
        rw [add_right_comm, hw2, zero_add]
      exact False.elim (hv x hx w hw he)

/-- Every thirty-point set containing zero admits a four-dimensional avoiding subspace. -/
theorem singleton_four_subspace (S : Finset EightSpace) (hzero : 0 ∈ S)
    (hcard : S.card = 30) :
    ∃ W : Submodule F₂ EightSpace, finrank F₂ W = 4 ∧ AvoidsNonzero S W := by
  classical
  have hstep : ∀ d : ℕ, d ≤ 4 → ∃ W : Submodule F₂ EightSpace,
      finrank F₂ W = d ∧ AvoidsNonzero S W := by
    intro d hd
    induction d with
    | zero =>
      refine ⟨⊥, ?_, ?_⟩
      · simp
      · intro x hx hxb
        simpa using hxb
    | succ d ih =>
      obtain ⟨W, hdim, hW⟩ := ih (by omega)
      have hsmall : S.card * 2 ^ finrank F₂ W < 256 := by
        rw [hcard, hdim]
        have hpow : 2 ^ d ≤ 8 := by
          have hd3 : d ≤ 3 := by omega
          exact (Nat.pow_le_pow_right (by decide) hd3)
        omega
      obtain ⟨W', hd', hW'⟩ := extend_avoiding_subspace S hzero W hW hsmall
      exact ⟨W', by omega, hW'⟩
  exact hstep 4 (by decide)


/-- Choose split coordinates whose first block parametrizes the avoiding four-space. -/
theorem coordinates_for_four_subspace (W : Submodule F₂ EightSpace)
    (hW : finrank F₂ W = 4) :
    ∃ e : DoubleBlock ≃ₗ[F₂] EightSpace,
      ∀ x : Block, e (Sum.elim x 0) ∈ W := by
  classical
  obtain ⟨C, hC⟩ := W.exists_isCompl
  have hCdim : finrank F₂ C = 4 := by
    have hh : finrank F₂ W + finrank F₂ C = finrank F₂ EightSpace :=
      Submodule.finrank_add_eq_of_isCompl hC
    have hdim8 : finrank F₂ EightSpace = 8 := by simp [EightSpace, Module.finrank_pi]
    rw [hW, hdim8] at hh
    omega
  let eW : Block ≃ₗ[F₂] W := LinearEquiv.ofFinrankEq _ _ (by
    simp [Block, Module.finrank_pi, hW])
  let eC : Block ≃ₗ[F₂] C := LinearEquiv.ofFinrankEq _ _ (by
    simp [Block, Module.finrank_pi, hCdim])
  let e : DoubleBlock ≃ₗ[F₂] EightSpace :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) F₂ F₂).trans
      ((eW.prodCongr eC).trans (Submodule.prodEquivOfIsCompl W C hC))
  refine ⟨e, ?_⟩
  intro x
  change ((eW x : W) : EightSpace) + ((eC 0 : C) : EightSpace) ∈ W
  simp

private theorem eight_add_self (x : EightSpace) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

/-- Geometric singleton-fiber selection, with a genuine invertible linear coordinate map. -/
theorem exists_singleton_coordinates (f : EightSpace → F₂) (hw : weight f = 30) :
    ∃ (p : EightSpace) (e : DoubleBlock ≃ₗ[F₂] EightSpace),
      fiber (fun z => f (p + e z)) 0 = delta 0 := by
  classical
  let S := Finset.univ.filter (fun x : EightSpace => f x = 1)
  have hScard : S.card = 30 := (weight_eq_support_card f).symm.trans hw
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hfp : f p = 1 := (Finset.mem_filter.mp hp).2
  let T := S.image (fun x => x + p)
  have hTcard : T.card = 30 := by
    rw [Finset.card_image_of_injective S (fun a b h => add_right_cancel h)]
    exact hScard
  have hzero : 0 ∈ T := Finset.mem_image.mpr ⟨p, hp, eight_add_self p⟩
  obtain ⟨W, hWdim, hW⟩ := singleton_four_subspace T hzero hTcard
  obtain ⟨e, he⟩ := coordinates_for_four_subspace W hWdim
  refine ⟨p, e, ?_⟩
  funext x
  by_cases hx : x = 0
  · subst x
    have h00 : Sum.elim (0 : Block) (0 : Block) = (0 : DoubleBlock) := by
      funext j
      cases j <;> rfl
    simp only [fiber, h00, map_zero, add_zero]
    simp [hfp, delta]
  · have hnot : f (p + e (Sum.elim x 0)) ≠ 1 := by
      intro hfx
      have hm : e (Sum.elim x 0) ∈ T := by
        apply Finset.mem_image.mpr
        refine ⟨p + e (Sum.elim x 0), ?_, ?_⟩
        · simp [S, hfx]
        · rw [add_right_comm, eight_add_self p, zero_add]
      have hz := hW _ hm (he x)
      have hez : Sum.elim x (0 : Block) = (0 : DoubleBlock) :=
        e.injective (by simpa using hz)
      apply hx
      funext i
      exact congrFun hez (.inl i)
    have hbit : f (p + e (Sum.elim x 0)) = 0 ∨ f (p + e (Sum.elim x 0)) = 1 := by
      generalize f (p + e (Sum.elim x 0)) = b
      fin_cases b <;> simp
    change f (p + e (Sum.elim x 0)) = delta 0 x
    rw [hbit.resolve_right hnot]
    simp [delta, hx]

end BooleanANF
