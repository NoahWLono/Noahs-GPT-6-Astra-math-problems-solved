/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
Reviewed adaptation from commit dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
Changes: pinned local imports and Lean 4.32 inertia/ramification API compatibility.
-/
import FunctionFieldPlaces
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.GroupTheory.ArchimedeanDensely
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField

variable (k K : Type*) [Field k] [Field K]

open MonoidWithZeroHom

/-- The ordered multiplicative group with zero `ℤᵐ⁰` has no nontrivial ordered monoid
automorphisms. -/
private noncomputable def withZeroMulIntLogAddEquiv
    (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) : ℤ ≃+ ℤ := by
  let f : ℤ →+ ℤ :=
    { toFun := fun z => WithZero.log (e (WithZero.exp z))
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [WithZero.exp_add, map_mul]
        rw [WithZero.log_mul]
        · simp
        · simp }
  refine AddEquiv.ofBijective f ?_
  constructor
  · intro x y h
    apply WithZero.exp_injective
    apply e.injective
    simpa [f] using congrArg WithZero.exp h
  · intro y
    refine ⟨WithZero.log (e.symm (WithZero.exp y)), ?_⟩
    dsimp [f]
    rw [WithZero.exp_log]
    · simp
    · simp

/-- A normalized discrete rank-one value group has a unique order-preserving normalization. -/
theorem orderMonoidIso_withZeroMulInt_eq_refl (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) :
    e = OrderMonoidIso.refl ℤᵐ⁰ := by
  have hmono : Monotone (withZeroMulIntLogAddEquiv e) := by
    intro x y hxy
    dsimp [withZeroMulIntLogAddEquiv]
    change WithZero.log (e (WithZero.exp x)) ≤
      WithZero.log (e (WithZero.exp y))
    apply WithZero.exp_le_exp.mp
    rw [WithZero.exp_log, WithZero.exp_log]
    · exact e.toOrderIso.monotone (WithZero.exp_le_exp.mpr hxy)
    · simp
    · simp
  rcases Int.addEquiv_eq_refl_or_neg (withZeroMulIntLogAddEquiv e) with h | h
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [← WithZero.exp_log hx]
      apply WithZero.exp_injective
      have ht := congrArg WithZero.exp
        (DFunLike.congr_fun h (WithZero.log x))
      simpa [withZeroMulIntLogAddEquiv] using ht
  · have hle := hmono (show (0 : ℤ) ≤ 1 by omega)
    rw [h] at hle
    norm_num at hle

/-- Any two order-preserving normalizations of the same value group are equal. -/
theorem orderMonoidIso_withZeroMulInt_unique {G : Type*}
    [LinearOrderedCommGroupWithZero G] (e f : G ≃*o ℤᵐ⁰) : e = f := by
  have h := orderMonoidIso_withZeroMulInt_eq_refl (e.symm.trans f)
  ext x
  have hx := DFunLike.congr_fun h (e x)
  simpa using hx.symm

/-- A coordinate-free place of `K/k`: a nontrivial valuation subring of `K` containing the
constant field, together with the proposition that its value group admits the discrete rank-one
normalization.  The normalization is stored only through `Nonempty`, so a place is determined by
its valuation subring rather than by a choice of uniformizer. -/
structure Place [Algebra k K] where
  /-- The valuation subring underlying the place. -/
  toValuationSubring : ValuationSubring K
  /-- A place is nontrivial. -/
  ne_top : toValuationSubring ≠ ⊤
  /-- Constants are integral at every place. -/
  triv_on_k : ∀ c : k, algebraMap k K c ∈ toValuationSubring
  /-- The value group is discrete of rank one, expressed without choosing a normalization. -/
  isDiscrete : Nonempty
    (ValueGroup₀ (.ofClass toValuationSubring.valuation) ≃*o ℤᵐ⁰)

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Two places are equal when their valuation subrings are equal. -/
@[ext]
theorem ext {v w : Place k K}
    (h : v.toValuationSubring = w.toValuationSubring) : v = w := by
  cases v
  cases w
  cases h
  rfl

/-- Places inherit the membership coercion of their valuation subrings. -/
instance : SetLike (Place k K) K where
  coe v := v.toValuationSubring
  coe_injective := by
    intro v w h
    exact ext (SetLike.coe_injective h)

@[simp]
theorem mem_toValuationSubring (v : Place k K) (x : K) :
    x ∈ v.toValuationSubring ↔ x ∈ v := Iff.rfl

/-- A normalization of the value group of a coordinate-free place. -/
noncomputable def normalization (v : Place k K) :
    ValueGroup₀ (.ofClass v.toValuationSubring.valuation) ≃*o ℤᵐ⁰ :=
  Classical.choice v.isDiscrete

/-- The normalized `ℤᵐ⁰`-valued valuation associated to a coordinate-free place. -/
noncomputable def valuation (v : Place k K) : Valuation K ℤᵐ⁰ :=
  v.toValuationSubring.valuation.restrict.map
    v.normalization.toMonoidWithZeroHom v.normalization.toOrderIso.monotone

/-- The normalized valuation is equivalent to the canonical valuation of the valuation
subring. -/
theorem valuation_isEquiv_canonical (v : Place k K) :
    v.valuation.IsEquiv v.toValuationSubring.valuation := by
  exact (Valuation.isEquiv_map_self_of_strictMono
    v.normalization.toMonoidWithZeroHom v.normalization.strictMono).trans
      v.toValuationSubring.valuation.isEquiv_restrict.symm

/-- Recovering the valuation subring from the normalized valuation gives the original place. -/
@[simp]
theorem valuationSubring_valuation (v : Place k K) :
    v.valuation.valuationSubring = v.toValuationSubring := by
  exact (Valuation.isEquiv_iff_valuationSubring _ _).mp
    v.valuation_isEquiv_canonical |>.trans
      v.toValuationSubring.valuationSubring_valuation

/-- The normalized valuation of a place is trivial on the constant field. -/
instance valuation_isTrivialOn (v : Place k K) : v.valuation.IsTrivialOn k where
  eq_one c hc := by
    let w := v.toValuationSubring.valuation
    have hc_le : w (algebraMap k K c) ≤ 1 := by
      rw [v.toValuationSubring.valuation_le_one_iff]
      exact v.triv_on_k c
    have hc_inv_le : w (algebraMap k K c⁻¹) ≤ 1 := by
      rw [v.toValuationSubring.valuation_le_one_iff]
      exact v.triv_on_k c⁻¹
    have hmap_ne : w (algebraMap k K c) ≠ 0 := by simp [hc]
    have hmap_pos : 0 < w (algebraMap k K c) := zero_lt_iff.mpr hmap_ne
    have hinv_le : (w (algebraMap k K c))⁻¹ ≤ 1 := by
      simpa only [map_inv₀, map_inv] using hc_inv_le
    have hw : w (algebraMap k K c) = 1 :=
      le_antisymm hc_le ((inv_le_one₀ hmap_pos).1 hinv_le)
    exact v.valuation_isEquiv_canonical.eq_one_iff_eq_one.mpr hw

/-- The normalized valuation of a place is nontrivial. -/
instance valuation_isNontrivial (v : Place k K) : v.valuation.IsNontrivial := by
  have hcanonical : v.toValuationSubring.valuation.IsNontrivial := by
    by_contra h
    exact v.ne_top (v.toValuationSubring.eq_top_iff.mpr h)
  exact Valuation.isNontrivial_of_isEquiv
    v.valuation_isEquiv_canonical.symm hcanonical

/-- The valuation ring itself, viewed as a `k`-algebra. -/
instance algebraValuationSubring (v : Place k K) : Algebra k v.toValuationSubring :=
  (algebraMap k K).codRestrict v.toValuationSubring (fun c ↦ v.triv_on_k c) |>.toAlgebra

/-- The residue field of a coordinate-free place. -/
abbrev residueField (v : Place k K) :=
  IsLocalRing.ResidueField v.toValuationSubring

/-- The intrinsic degree of a place is the dimension of its residue field over `k`. -/
noncomputable def degree (v : Place k K) : ℕ :=
  Module.finrank k v.residueField

end Place


end FunctionField
#print axioms FunctionField.Place.valuationSubring_valuation
