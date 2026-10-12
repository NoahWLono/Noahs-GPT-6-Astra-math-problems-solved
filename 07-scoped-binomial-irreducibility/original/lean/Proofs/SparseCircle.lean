import FiniteOrderRigidity
import PowerSamples

/-! The finite-circle obstruction for any sparse exponent coprime to the degree. -/
set_option autoImplicit false
open scoped BigOperators
open Finset Complex Set
open PillaiFourier PillaiTaylorFourier PillaiSamples PillaiFiniteOrder
namespace PillaiSparseCircle
variable {n : ℕ} [NeZero n] {ζ : ℂ}

lemma rootChar_injective (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (rootChar hζ.pow_eq_one) := by
  intro i j h
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) h)

/-- Equal real coordinates on the unit circle mean equal or conjugate roots. -/
lemma circleX_eq_iff (hζ : IsPrimitiveRoot ζ n) (i j : ZMod n) :
    circleX hζ.pow_eq_one i=circleX hζ.pow_eq_one j ↔ i=j ∨ i= -j := by
  constructor
  · intro h
    have hnorm (t : ZMod n) : (rootChar hζ.pow_eq_one t).re^2+
        (rootChar hζ.pow_eq_one t).im^2=1 := by
      have hh := congrArg (fun x : ℝ ↦ x^2) (rootChar_norm hζ.pow_eq_one t)
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hh
      simpa [pow_two] using hh
    have him : (rootChar hζ.pow_eq_one i).im^2=(rootChar hζ.pow_eq_one j).im^2 := by
      dsimp [circleX] at h
      have hi := hnorm i
      rw [h] at hi
      linarith [hnorm j]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp him with him | him
    · exact Or.inl (rootChar_injective hζ (Complex.ext h him))
    · right
      apply rootChar_injective hζ
      rw [← rootChar_conj]
      apply Complex.ext
      · exact h
      · simpa using him
  · rintro (rfl | rfl)
    · rfl
    · simp only [circleX,← rootChar_conj,Complex.conj_re]

lemma circleX_zero (hζ : ζ^n=1) : circleX hζ 0=1 := by simp [circleX]

lemma circleX_ne_one (hζ : IsPrimitiveRoot ζ n) {i : ZMod n} (hi : i≠0) :
    circleX hζ.pow_eq_one i≠1 := by
  rw [← circleX_zero hζ.pow_eq_one]
  simp only [ne_eq,circleX_eq_iff hζ]
  simpa using hi

/-- The finite circle has at least three distinct real coordinates when n≥5. -/
lemma circleX_three_distinct (hζ : IsPrimitiveRoot ζ n) (hn : 5≤n) :
    circleX hζ.pow_eq_one 0≠circleX hζ.pow_eq_one 1 ∧
    circleX hζ.pow_eq_one 0≠circleX hζ.pow_eq_one 2 ∧
    circleX hζ.pow_eq_one 1≠circleX hζ.pow_eq_one 2 := by
  have h₁ := small_natCast_ne_zero hn 1 (by omega) (by omega)
  have h₂ := small_natCast_ne_zero hn 2 (by omega) (by omega)
  have h₃ := small_natCast_ne_zero hn 3 (by omega) (by omega)
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at h₁ h₂ h₃
  simp only [ne_eq,circleX_eq_iff hζ]
  refine ⟨?_,?_,?_⟩
  · rintro (h | h)
    · apply h₁; linear_combination -h
    · apply h₁; linear_combination h
  · rintro (h | h)
    · apply h₂; linear_combination -h
    · apply h₂; linear_combination h
  · rintro (h | h)
    · apply h₁; linear_combination -h
    · apply h₃; linear_combination h

/-- Finite circle permutation plus a nonconstant affine target is incompatible with a power. -/
theorem circle_power_affine_impossible (hζ : IsPrimitiveRoot ζ n) (hn : 5≤n)
    (m : ℕ) (hm : 2≤m) (j : ZMod n) (hj : IsUnit j) (U V C D : ℝ) (hD : D≠0)
    (hbase : ∀ i : ZMod n, 0≤U+V*circleX hζ.pow_eq_one i)
    (heq : ∀ i : ZMod n, (U+V*circleX hζ.pow_eq_one (i*j))^m=
      C+D*circleX hζ.pow_eq_one i) : False := by
  classical
  let S : Finset ℝ := univ.image (circleX hζ.pow_eq_one)
  let pt (i : ZMod n) : S := ⟨circleX hζ.pow_eq_one i,mem_image.mpr ⟨i,mem_univ i,rfl⟩⟩
  have hthree := circleX_three_distinct hζ hn
  have hV : V≠0 := by
    intro hV
    have h₀ := heq 0
    have h₁ := heq 1
    simp only [hV,zero_mul,add_zero] at h₀ h₁
    apply hthree.1
    exact mul_left_cancel₀ hD (add_left_cancel (h₀.symm.trans h₁))
  have hrange : Set.range (fun x : S ↦ (U+V*(x : ℝ))^m)=
      Set.range (fun x : S ↦ C+D*(x : ℝ)) := by
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨t,_,ht⟩ := mem_image.mp x.property
      obtain ⟨i,hi⟩ := (IsUnit.isUnit_iff_mulRight_bijective.mp hj).2 t
      change i*j=t at hi
      refine ⟨pt i,?_⟩
      change C+D*circleX hζ.pow_eq_one i=(U+V*(x : ℝ))^m
      rw [← heq i,hi,ht]
    · rintro ⟨x,rfl⟩
      obtain ⟨i,_,hi⟩ := mem_image.mp x.property
      refine ⟨pt (i*j),?_⟩
      change (U+V*circleX hζ.pow_eq_one (i*j))^m=C+D*(x : ℝ)
      rw [heq i,hi]
  refine finite_power_affine_impossible S m hm U V C D hV hD ?_ hrange (pt 0) ?_ ?_ ?_
    (pt 0) (pt 1) (pt 2) ?_ ?_ ?_
  · intro x
    obtain ⟨i,_,hi⟩ := mem_image.mp x.property
    simpa only [hi] using hbase i
  · intro x
    obtain ⟨i,_,hi⟩ := mem_image.mp x.property
    change (x : ℝ)≤circleX hζ.pow_eq_one 0
    rw [circleX_zero,← hi]
    exact (abs_le.mp (circleX_bound _ _)).2
  · simpa only [pt,zero_mul] using heq 0
  · refine ⟨pt 1,?_⟩
    change circleX hζ.pow_eq_one 1<circleX hζ.pow_eq_one 0
    rw [circleX_zero]
    apply lt_of_le_of_ne (abs_le.mp (circleX_bound _ _)).2
    simpa only [circleX_zero] using hthree.1.symm
  · intro h; exact hthree.1 (congrArg Subtype.val h)
  · intro h; exact hthree.2.1 (congrArg Subtype.val h)
  · intro h; exact hthree.2.2 (congrArg Subtype.val h)

lemma norm_add_square (a b : ℝ) (w : ℂ) (hw : ‖w‖=1) :
    ‖(a : ℂ)+(b : ℂ)*w‖^2=a^2+b^2+2*a*b*w.re := by
  have h := norm_shift_square a b (-1) w hw (Or.inr rfl)
  norm_num only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,neg_mul,sub_neg_eq_add,one_mul] at h
  rw [h]
  ring

/-- No sparse two-term family can satisfy all conjugate power equations when its exponent
is a unit modulo n. The two real coefficients are unrestricted. -/
theorem sparse_power_impossible (hζ : IsPrimitiveRoot ζ n) (hn : 5≤n)
    (m : ℕ) (hm : 2≤m) (j : ZMod n) (hj : IsUnit j) (a b A ρ s : ℝ)
    (hA : 0<A) (hρ : 0<ρ) (hs : s=1 ∨ s= -1)
    (heq : ∀ i : ZMod n, ((a : ℂ)+(b : ℂ)*rootChar hζ.pow_eq_one (i*j))^m=
      (A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i) : False := by
  apply circle_power_affine_impossible hζ hn m hm j hj (a^2+b^2) (2*a*b)
    (A^2+ρ^2) (-2*s*A*ρ)
  · rcases hs with rfl | rfl <;> positivity
  · intro i
    dsimp only [circleX]
    rw [← norm_add_square a b _ (rootChar_norm _ _)]
    exact sq_nonneg _
  · intro i
    have hh : (‖(a : ℂ)+(b : ℂ)*rootChar hζ.pow_eq_one (i*j)‖^2)^m=
        ‖(A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i‖^2 := by
      rw [← pow_mul,Nat.mul_comm 2 m,pow_mul,← norm_pow,heq i]
    rw [norm_add_square a b _ (rootChar_norm _ _),norm_shift_square A ρ s _ (rootChar_norm _ _) hs] at hh
    dsimp only [circleX]
    convert hh using 1
    ring

end PillaiSparseCircle
