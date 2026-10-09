import BooleanANFWeight

namespace BooleanANF
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Hamming weight one is equivalent to an actual singleton indicator. -/
theorem exists_delta_of_weight_one {f : (ι → F₂) → F₂} (hw : weight f = 1) :
    ∃ a, f = delta a := by
  rw [weight_eq_support_card] at hw
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hw
  refine ⟨a, ?_⟩
  funext x
  have hx : f x = 1 ↔ x = a := by
    have := Finset.ext_iff.mp ha x
    simpa using this
  by_cases h : x = a
  · rw [show f x = 1 from hx.mpr h]
    simp [delta, h]
  · have hzero : f x = 0 := by
      have hb : f x = 0 ∨ f x = 1 := by
        generalize f x = b
        fin_cases b <;> simp_all
      exact hb.resolve_right (fun hf => h (hx.mp hf))
    simp [delta, h, hzero]

/-- The top ANF coefficient is exactly the parity of Hamming weight. -/
theorem weight_cast_eq_top (f : (ι → F₂) → F₂) :
    (weight f : F₂) = coefficient f Finset.univ := by
  simp [weight, coefficient_top_eq_sum, ZMod.natCast_zmod_val]

theorem weight_odd_of_top_one {f : (ι → F₂) → F₂}
    (ht : coefficient f Finset.univ = 1) : weight f % 2 = 1 := by
  have h := congrArg ZMod.val ((weight_cast_eq_top f).trans ht)
  simpa [ZMod.val_natCast] using h

/-- Odd rows in a sixteen-row table of weight thirty leave at most seven nonsingletons. -/
theorem nonsingleton_fiber_count {f : DoubleBlock → F₂} (hw : weight f = 30)
    (ho : ∀ y : Block, weight (fiber f y) % 2 = 1) :
    (Finset.univ.filter (fun y : Block => weight (fiber f y) ≠ 1)).card ≤ 7 := by
  have hrow (y : Block) :
      1 + 2 * (if weight (fiber f y) ≠ 1 then 1 else 0) ≤ weight (fiber f y) := by
    have hp := ho y
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Block)) => hrow y)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hcount : (∑ y : Block, if weight (fiber f y) ≠ 1 then 1 else 0) =
      (Finset.univ.filter (fun y : Block => weight (fiber f y) ≠ 1)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcount] at hs
  change (∑ _y : Block, 1) + 2 * _ ≤ ∑ y : Block, weight (fun x => f (Sum.elim x y)) at hs
  rw [weight_fibers, hw] at hs
  norm_num [Block, Fintype.card_fun, ZMod.card] at hs
  simpa only [ne_eq] using (show (Finset.univ.filter (fun y : Block =>
    ¬ weight (fiber f y) = 1)).card ≤ 7 by omega)

/-- The normalized residual vanishes in each weight-one row. -/
theorem residual_zero_of_weight_one (f : DoubleBlock → F₂) (y : Block)
    (hw : weight (fiber f y) = 1) : fiber (residual f) y = 0 := by
  obtain ⟨a, ha⟩ := exists_delta_of_weight_one hw
  rw [residual_fiber, normalized_singleton f y a ha]
  funext x
  exact CharTwo.add_self_eq_zero _

/-- The key sparse-row bound after simultaneous shear normalization. -/
theorem residual_active_count {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4)
    (hw : weight f = 30) (y₀ a : Block) (hsingle : fiber f y₀ = delta a) :
    (Finset.univ.filter (fun y : Block => fiber (residual f) y ≠ 0)).card ≤ 7 := by
  have ho (y : Block) : weight (fiber f y) % 2 = 1 :=
    weight_odd_of_top_one (top_one_of_singleton hf y₀ a hsingle y)
  apply le_trans (Finset.card_le_card ?_) (nonsingleton_fiber_count hw ho)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact fun h => hy (residual_zero_of_weight_one f y h)

end BooleanANF
