import QuadraticWalshShift
namespace QuadraticWalshRadical
open FastWalsh QuadraticWalshShift

/-- Coordinate dot products separate binary vectors. -/
theorem binaryDot_separates (a : BitVec n)
    (h : ∀ u, binaryDot u a = false) : a = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [← BitVec.cons_msb_setWidth a] at h ⊢
    generalize a.msb = c at h ⊢
    generalize a.setWidth n = d at h ⊢
    have hd : d = 0 := ih d (by
      intro u
      have hh := h (BitVec.cons false u)
      simpa only [binaryDot_cons, Bool.false_and, Bool.xor_false] using hh)
    have hc := h (BitVec.cons true (0 : BitVec n))
    simp only [binaryDot_cons, binaryDot_zero_left, Bool.true_and, Bool.false_xor] at hc
    rw [hc, hd]
    exact BitVec.false_cons_zero

theorem binaryDot_detect (a : BitVec n) (ha : a ≠ 0) :
    ∃ u, binaryDot u a = true := by
  classical
  apply Classical.byContradiction
  intro h
  apply ha
  apply binaryDot_separates
  intro u
  cases hu : binaryDot u a
  · rfl
  · exact False.elim (h ⟨u, hu⟩)

/-- A radical direction with odd translation phase annihilates an actual coefficient. -/
theorem booleanWalsh_zero_of_translation (q : BitVec n → Bool) (a u : BitVec n)
    (htrans : ∀ x, q (x ^^^ a) = (q x ^^ q a))
    (hphase : (q a ^^ binaryDot u a) = true) : booleanWalsh q u = 0 := by
  have hpoint : ∀ x, signed (q (x ^^^ a) ^^ binaryDot u (x ^^^ a)) 1 =
      -signed (q x ^^ binaryDot u x) 1 := by
    intro x
    rw [htrans, binaryDot_xor_right]
    cases hx : q x <;> cases ha : q a <;> cases hu : binaryDot u x <;> cases hv : binaryDot u a <;>
      simp_all [signed]
  have hs := sumDomain_xor (fun x => signed (q x ^^ binaryDot u x) 1) a
  simp only [hpoint, sumDomain_neg] at hs
  unfold booleanWalsh
  omega

theorem coefficient_radical_of_basis
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (a : BitVec n)
    (hcheck : ∀ e ∈ basis n, coefficientPolar cs b a e = false) :
    ∀ x, coefficientPolar cs b a x = false := by
  exact additive_eq_of_basis (coefficientPolar cs b a) (fun _ => false)
    (coefficientPolar_add_right cs b a) (by intros; rfl) hcheck

/-- An explicitly nonzero radical vector yields some zero actual Walsh coefficient. -/
theorem quadratic_zero_coefficient_of_radical
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (a : BitVec n)
    (ha : a ≠ 0)
    (hcheck : ∀ e ∈ basis n, coefficientPolar cs b a e = false) :
    ∃ u : BitVec n, walsh (quadratic cs) b u = 0 := by
  have htrans : ∀ x, quadraticComponent cs b (x ^^^ a) =
      (quadraticComponent cs b x ^^ quadraticComponent cs b a) := by
    intro x
    rw [quadraticComponent_translate, coefficient_radical_of_basis cs b a hcheck]
    exact Bool.xor_false _
  have hphase : ∃ u : BitVec n,
      (quadraticComponent cs b a ^^ binaryDot u a) = true := by
    cases hq : quadraticComponent cs b a
    · obtain ⟨u, hu⟩ := binaryDot_detect a ha
      exact ⟨u, by simp [hq, hu]⟩
    · exact ⟨0, by rw [binaryDot_zero_left]; rfl⟩
  obtain ⟨u, hu⟩ := hphase
  refine ⟨u, ?_⟩
  rw [walsh_quadratic_eq]
  exact booleanWalsh_zero_of_translation _ a u htrans hu

theorem quadratic_not_bent_of_radical
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (a : BitVec n)
    (ha : a ≠ 0)
    (hcheck : ∀ e ∈ basis n, coefficientPolar cs b a e = false) :
    ¬IsBent (quadratic cs : BitVec n → BitVec m) b := by
  intro hbent
  obtain ⟨u, hu⟩ := quadratic_zero_coefficient_of_radical cs b a ha hcheck
  have hh := hbent u
  rw [hu] at hh
  have hn : 0 < (2^n : Nat) := Nat.pow_pos (by decide)
  omega

/-- Exactly n executable polar checks for the supplied radical witness. -/
def radicalCheck (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (a : BitVec n) : Bool :=
  (basis n).all fun e => coefficientPolar cs b a e == false

theorem radicalCheck_correct
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (a : BitVec n) :
    radicalCheck cs b a = true ↔ ∀ e ∈ basis n, coefficientPolar cs b a e = false := by
  simp [radicalCheck, List.all_eq_true, beq_iff_eq]

theorem quadratic_not_bent_certificate
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (a : BitVec n)
    (ha : a ≠ 0) (hcheck : radicalCheck cs b a = true) :
    ¬IsBent (quadratic cs : BitVec n → BitVec m) b :=
  quadratic_not_bent_of_radical cs b a ha ((radicalCheck_correct cs b a).mp hcheck)

#print axioms binaryDot_detect
#print axioms quadratic_zero_coefficient_of_radical
#print axioms quadratic_not_bent_certificate
end QuadraticWalshRadical
