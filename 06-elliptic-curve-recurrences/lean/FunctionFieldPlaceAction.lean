/-
The normalization argument below adapts Guanghao Li's Apache-2.0
Place.ofChart_valuation_eq proof from commit dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
The automorphism action is a local extension of that interface.
-/
import FunctionFieldPlaceEquiv

/-! Actual pullback of places by constant-field automorphisms. -/
namespace FunctionField
noncomputable section
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom Chart
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Construct an intrinsic place from a nontrivial discrete integer-valued valuation. -/
def Place.ofValuation (q : Valuation K ℤᵐ⁰) [q.IsNontrivial]
    (hc : ∀ c : k, q (algebraMap k K c) ≤ 1) : Place k K := by
  letI : q.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' q
  refine { toValuationSubring := q.valuationSubring
           ne_top := fun h => (Valuation.valuationSubring_eq_top_iff q).mp h inferInstance
           triv_on_k := fun c => hc c
           isDiscrete := ?_ }
  let h := Valuation.isEquiv_valuation_valuationSubring q
  exact ⟨h.orderMonoidIso.symm.trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)⟩

theorem Place.ofValuation_valuation (q : Valuation K ℤᵐ⁰) [q.IsNontrivial]
    (hc : ∀ c : k, q (algebraMap k K c) ≤ 1) (hq : Function.Surjective q) :
    (Place.ofValuation q hc).valuation = q := by
  letI : q.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' q
  let V := q.valuationSubring
  let h := Valuation.isEquiv_valuation_valuationSubring q
  let e : ValueGroup₀ (.ofClass V.valuation) ≃*o ℤᵐ⁰ :=
    h.orderMonoidIso.symm.trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
  have hn : (Place.ofValuation q hc).normalization = e :=
    orderMonoidIso_withZeroMulInt_unique _ _
  ext x
  change (Place.ofValuation q hc).normalization (V.valuation.restrict x) = q x
  rw [hn]
  change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
      (h.orderMonoidIso.symm (V.valuation.restrict x)) = q x
  rw [show h.orderMonoidIso.symm (V.valuation.restrict x) = q.restrict x by
    exact h.orderMonoidIso.symm_apply_eq.mpr (h.orderMonoidIso_spec x).symm]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hq x

variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

theorem Place.valuation_surjective (v : Place k K) : Function.Surjective v.valuation := by
  obtain ⟨w, rfl⟩ := (chartToPlace k K).surjective v
  rw [placeValuation_eq]
  cases w with
  | inl w => exact w.valuation_surjective K
  | inr w => exact w.valuation_surjective K

instance Place.comap_nontrivial (v : Place k K) (e : K ≃ₐ[k] K) :
    (v.valuation.comap e.toRingHom).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ := (inferInstance : v.valuation.IsNontrivial).exists_val_nontrivial
  refine ⟨e.symm x, ?_, ?_⟩
  · simpa using hx0
  · simpa using hx1

def Place.pullback (e : K ≃ₐ[k] K) (v : Place k K) : Place k K :=
  Place.ofValuation (v.valuation.comap e.toRingHom) (fun c => by
    change v.valuation (e (algebraMap k K c)) ≤ 1
    rw [e.commutes]
    rw [← Valuation.mem_valuationSubring_iff, v.valuationSubring_valuation]
    exact v.triv_on_k c)

theorem Place.pullback_valuation (e : K ≃ₐ[k] K) (v : Place k K) :
    (v.pullback e).valuation = v.valuation.comap e.toRingHom :=
  Place.ofValuation_valuation _ _ (v.valuation_surjective.comp e.surjective)

theorem Place.pullback_symm (e : K ≃ₐ[k] K) (v : Place k K) :
    (v.pullback e).pullback e.symm = v := by
  apply Place.ext
  rw [← Place.valuationSubring_valuation, ← v.valuationSubring_valuation]
  congr 1
  rw [Place.pullback_valuation, Place.pullback_valuation]
  ext x
  exact congrArg v.valuation (e.apply_symm_apply x)

/-- Every field automorphism over the constants genuinely permutes all places. -/
def placePullbackEquiv (e : K ≃ₐ[k] K) : Place k K ≃ Place k K where
  toFun := Place.pullback e
  invFun := Place.pullback e.symm
  left_inv := Place.pullback_symm e
  right_inv := Place.pullback_symm e.symm

/-- The corresponding permutation on the actual finite/infinite coordinate places. -/
def chartPullbackEquiv (e : K ≃ₐ[k] K) : PlaceA k K ≃ PlaceA k K :=
  (chartToPlace k K).trans ((placePullbackEquiv e).trans (chartToPlace k K).symm)

theorem chartPullback_valuation (e : K ≃ₐ[k] K) (v : PlaceA k K) (f : K) :
    placeValuation k K (chartPullbackEquiv e v) f = placeValuation k K v (e f) := by
  rw [← placeValuation_eq, ← placeValuation_eq]
  change ((chartToPlace k K) ((chartToPlace k K).symm
    (Place.pullback e ((chartToPlace k K) v)))).valuation f = _
  rw [Equiv.apply_symm_apply, Place.pullback_valuation]
  rfl


/-- Exact principal-divisor covariance under the constructed place permutation. -/
theorem principalDivisorA_pullback (e : K ≃ₐ[k] K) (f : Kˣ) (v : PlaceA k K) :
    principalDivisorA k K (Additive.ofMul (Units.map e.toMonoidHom f)) v =
      principalDivisorA k K (Additive.ofMul f) (chartPullbackEquiv e v) := by
  have h := chartPullback_valuation e v (f : K)
  have hf := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul f)
    (chartPullbackEquiv e v)
  change placeValuation k K (chartPullbackEquiv e v) (f : K) = _ at hf
  rw [hf] at h
  have he := placeValuation_eq_exp_neg_principalDivisor k K
    (Additive.ofMul (Units.map e.toMonoidHom f)) v
  change placeValuation k K v (e (f : K)) = _ at he
  exact neg_injective (WithZero.exp_injective (he.symm.trans h.symm))

end
end FunctionField
#print axioms FunctionField.chartPullback_valuation

#print axioms FunctionField.principalDivisorA_pullback
