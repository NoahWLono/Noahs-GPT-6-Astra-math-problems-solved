import EllipticHeightNormalization

/-! The elementary integral quadratic-form argument, for later application
to the actual elliptic point height. -/
namespace Astra01.QuadraticHeight
variable {G : Type*} [AddCommGroup G] (h : G → ℤ)
variable (hpar : ∀ P Q, h (P+Q) + h (P-Q) = 2*h P + 2*h Q)
include hpar

theorem nsmul_add (n : ℕ) (P Q : G) :
    h (n • P + Q) = (n : ℤ)^2*h P + (n : ℤ)*(h (P+Q)-h P-h Q)+h Q := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more n hn hn1 =>
    have hp : ((n+1) • P + Q) + P = (n+2) • P + Q := by
      simp only [add_nsmul, one_nsmul, two_nsmul]
      abel
    have hm : ((n+1) • P + Q) - P = n • P + Q := by
      simp only [add_nsmul, one_nsmul]
      abel
    have he := hpar ((n+1) • P + Q) P
    rw [hp,hm,hn,hn1] at he
    push_cast at *
    linear_combination he

theorem nsmul (hzero : h 0 = 0) (n : ℕ) (P : G) : h (n • P) = (n : ℤ)^2*h P := by
  simpa [hzero] using nsmul_add h hpar n P 0

theorem two_nsmul (hzero : h 0 = 0) (n m : ℕ) (P Q : G) :
    h (n • P + m • Q) = (n : ℤ)^2*h P +
      (n : ℤ)*(m : ℤ)*(h (P+Q)-h P-h Q)+(m : ℤ)^2*h Q := by
  rw [nsmul_add h hpar n P (m • Q)]
  have he := nsmul_add h hpar m Q P
  rw [add_comm (m • Q) P, add_comm Q P] at he
  rw [he, nsmul h hpar hzero]
  ring

/-- Nonnegativity on the group forces the upper Cauchy–Schwarz discriminant
bound. The critical rational ratio is tested by explicit integer multiples. -/
theorem upper_discriminant (hzero : h 0 = 0) (hnonneg : ∀ P, 0 ≤ h P)
    (P Q : G) (hP : 0 < h P) :
    h (P-Q)-h P-h Q ≤ 0 ∨ (h (P-Q)-h P-h Q)^2 ≤ 4*h P*h Q := by
  let t := h (P-Q)-h P-h Q
  by_cases ht : t ≤ 0
  · exact Or.inl ht
  · have htpos : 0 < t := lt_of_not_ge ht
    have hn : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
    have hm : ((2*h P).toNat : ℤ) = 2*h P := Int.toNat_of_nonneg (by omega)
    have hb : h (P+Q)-h P-h Q = -t := by
      have he := hpar P Q
      dsimp [t]
      linarith
    have he := hnonneg (t.toNat • P + (2*h P).toNat • Q)
    rw [two_nsmul h hpar hzero,hn,hm,hb] at he
    have hprod : 0 ≤ h P * (4*h P*h Q-t^2) := by
      convert he using 1 <;> ring
    have hdisc := nonneg_of_mul_nonneg_right hprod hP
    right
    change t^2 ≤ 4*h P*h Q
    linarith
end Astra01.QuadraticHeight
#print axioms Astra01.QuadraticHeight.upper_discriminant
