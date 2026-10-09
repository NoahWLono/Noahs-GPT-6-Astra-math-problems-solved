import SingletonFiberCount

namespace BooleanANF
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Below the top degree, the support cardinality is even. -/
theorem HasDegreeLE.weight_even {f : (ι → F₂) → F₂} {d : ℕ}
    (hf : HasDegreeLE f d) (hd : d < Fintype.card ι) : weight f % 2 = 0 := by
  have ht : coefficient f Finset.univ = 0 := hf _ (by simpa using hd)
  have h := congrArg ZMod.val ((weight_cast_eq_top f).trans ht)
  simpa [ZMod.val_natCast] using h

/-- Exact support cardinality of a squarefree Boolean monomial. -/
theorem weight_monomial (s : Finset ι) :
    weight (monomial s) = 2 ^ (Fintype.card ι - s.card) := by
  let e : Finset ι ≃ (ι → F₂) :=
    { toFun := point, invFun := support,
      left_inv := support_point, right_inv := point_support }
  rw [← weight_equiv (monomial s) e, weight_eq_support_card]
  have he : (Finset.univ.filter (fun t : Finset ι => monomial s (e t) = 1)) =
      (Finset.univ \ s).powerset.image (s ∪ ·) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    change (if s ⊆ support (point t) then (1 : F₂) else 0) = 1 ↔ _
    simp only [support_point, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
    constructor
    · intro ht
      exact ⟨t \ s, Finset.sdiff_subset_sdiff (Finset.subset_univ _) (by rfl),
        Finset.union_sdiff_of_subset ht⟩
    · rintro ⟨v, hv, rfl⟩
      exact Finset.subset_union_left
  rw [he, Finset.card_image_iff.mpr]
  · rw [Finset.card_powerset, Finset.card_sdiff (Finset.subset_univ s), Finset.card_univ]
  · intro u hu v hv huv
    simp only [Finset.mem_coe, Finset.mem_powerset] at hu hv
    have hd1 : Disjoint s u := Finset.disjoint_sdiff.mono_right hu
    have hd2 : Disjoint s v := Finset.disjoint_sdiff.mono_right hv
    change s ⊔ u = s ⊔ v at huv
    rw [← hd1.sup_sdiff_cancel_left, ← hd2.sup_sdiff_cancel_left, huv]

/-- On seven variables, adding cubic functions of weight divisible by four
preserves that divisibility. -/
theorem cubic_seven_add_mod_four {f g : (Fin 7 → F₂) → F₂}
    (hf : HasDegreeLE f 3) (hg : HasDegreeLE g 3)
    (hwf : weight f % 4 = 0) (hwg : weight g % 4 = 0) :
    weight (fun x => f x + g x) % 4 = 0 := by
  have he := (hf.mul hg).weight_even (by decide)
  have h := weight_add f g
  omega

/-- Actual canonical cubic Boolean functions on seven variables have support
cardinality divisible by four. -/
theorem cubic_seven_weight_mod_four {f : (Fin 7 → F₂) → F₂}
    (hf : HasDegreeLE f 3) : weight f % 4 = 0 := by
  let term (s : Finset (Fin 7)) (x : Fin 7 → F₂) := coefficient f s * monomial s x
  have hd (s : Finset (Fin 7)) : HasDegreeLE (term s) 3 := by
    by_cases hs : s.card ≤ 3
    · exact ((degree_monomial s).mono hs).smul _
    · have hc := hf s (by omega)
      simp only [term, hc, zero_mul]
      exact degree_zero 3
  have hw (s : Finset (Fin 7)) : weight (term s) % 4 = 0 := by
    by_cases hs : s.card ≤ 3
    · have hm := weight_monomial s
      have hm4 : weight (monomial s) % 4 = 0 := by
        simp only [Fintype.card_fin] at hm
        interval_cases h : s.card <;> norm_num [h] at hm ⊢ <;> omega
      have hc : coefficient f s = 0 ∨ coefficient f s = 1 := by
        generalize coefficient f s = c
        fin_cases c <;> simp_all
      rcases hc with hc | hc
      · simp [term, hc, weight]
      · simpa [term, hc] using hm4
    · simp [term, hf s (by omega), weight]
  have hsum (I : Finset (Finset (Fin 7))) :
      weight (fun x => ∑ s ∈ I, term s x) % 4 = 0 := by
    induction I using Finset.induction_on with
    | empty => simp [weight]
    | @insert s I hs ih =>
      simp only [Finset.sum_insert hs]
      exact cubic_seven_add_mod_four (hd s)
        (HasDegreeLE.sum I term 3 (fun t _ => hd t)) (hw s) ih
  have hrepr : (fun x => ∑ s : Finset (Fin 7), term s x) = f :=
    funext (reconstruction_all f)
  simpa only [hrepr] using hsum Finset.univ

end BooleanANF
