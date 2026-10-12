import ConjugateEquation
import Mathlib.FieldTheory.Finite.Basic

/-! Actual integer-polynomial descent and Frobenius reduction by a monic binomial. -/
set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open PillaiResultant PillaiConjugates
namespace PillaiFrobenius
variable {n : ℕ} [NeZero n]

/-- A real power equation gives divisibility in Z[X], not merely in Q[X]. -/
theorem integer_relation_dvd (ρ : ℝ) (k : ℤ) (hρ : ρ^n=(k : ℝ))
    (hirr : Irreducible ((pureBinomial n k).map (Int.castRingHom ℚ)))
    (c : ZMod n → ℤ) (m : ℕ) (A s : ℤ)
    (heq : (∑ j : ZMod n, (c j : ℝ)*ρ^j.val)^m=(A : ℝ)-(s : ℝ)*ρ) :
    pureBinomial n k ∣ (coefficientPolynomial c)^m-C A+C s*X := by
  apply (Polynomial.map_dvd_map (Int.castRingHom ℚ) (by exact Int.cast_injective)
    (monic_X_pow_sub_C k (NeZero.ne n))).mp
  change (pureBinomial n k).map (Int.castRingHom ℚ) ∣ _
  rw [pureBinomial_eq_minpoly ρ k hρ hirr]
  apply minpoly.dvd ℚ ρ
  rw [eval_ratMap_real]
  simp only [eval₂_add,eval₂_sub,eval₂_pow,eval₂_mul,eval₂_C,eval₂_X,
    Int.coe_castRingHom,coefficientPolynomial_real_eval]
  linarith

omit [NeZero n] in
lemma binomial_dvd_power_reduction {R : Type*} [CommRing R] (k : R) (d : ℕ) :
    (X : R[X])^n-C k ∣ X^d-C (k^(d/n))*X^(d%n) := by
  have h := dvd_mul_of_dvd_left (sub_dvd_pow_sub_pow ((X : R[X])^n) (C k) (d/n))
    ((X : R[X])^(d%n))
  convert h using 1
  rw [sub_mul,← pow_mul,← pow_add,← map_pow]
  congr 2
  exact (Nat.div_add_mod d n).symm

/-- Canonical reduced Frobenius polynomial; every exponent is strictly below n. -/
noncomputable def reduced (q : ℕ) (k : ZMod q) (c : ZMod n → ZMod q) : (ZMod q)[X] :=
  ∑ j : ZMod n, C (c j*k^(j.val*q/n))*X^(j.val*q%n)

lemma reduced_degree_lt (q : ℕ) (k : ZMod q) (c : ZMod n → ZMod q) :
    (reduced q k c).degree < n := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
  intro j _
  exact (degree_C_mul_X_pow_le _ _).trans_lt
    (WithBot.coe_lt_coe.mpr (Nat.mod_lt _ (NeZero.pos n)))

/-- Frobenius plus monic division gives an exact polynomial identity in the residue field. -/
theorem reduced_relation (q : ℕ) [Fact q.Prime] (hn : 1<n) (k A s : ℤ)
    (c : ZMod n → ℤ)
    (hd : pureBinomial n k ∣ (coefficientPolynomial c)^q-C A+C s*X) :
    reduced q (k : ZMod q) (fun j ↦ (c j : ZMod q)) = C (A : ZMod q)-C (s : ZMod q)*X := by
  let f : (ZMod q)[X] := X^n-C (k : ZMod q)
  let P : (ZMod q)[X] := ∑ j : ZMod n, C (c j : ZMod q)*X^j.val
  let L : (ZMod q)[X] := C (A : ZMod q)-C (s : ZMod q)*X
  have hd' : f ∣ P^q-L := by
    have hh := Polynomial.map_dvd (Int.castRingHom (ZMod q)) hd
    have hh' : f ∣ P^q-C (A : ZMod q)+C (s : ZMod q)*X := by
      simpa only [f,P,pureBinomial,coefficientPolynomial,Polynomial.map_sub,Polynomial.map_add,
        Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Polynomial.map_sum,
        Int.coe_castRingHom] using hh
    convert hh' using 1
    dsimp [L]
    ring
  have hP : P^q = ∑ j : ZMod n, C (c j : ZMod q)*X^(j.val*q) := by
    simp only [P,sum_pow_char,mul_pow,← map_pow,ZMod.pow_card,← pow_mul]
  have hred : f ∣ P^q-reduced q (k : ZMod q) (fun j ↦ (c j : ZMod q)) := by
    rw [hP,reduced,← sum_sub_distrib]
    apply dvd_sum
    intro j _
    have h := dvd_mul_of_dvd_right (binomial_dvd_power_reduction (n := n) (k : ZMod q) (j.val*q))
      (C (c j : ZMod q))
    convert h using 1
    simp only [map_mul,mul_sub,mul_assoc]
  have hdiff : f ∣ reduced q (k : ZMod q) (fun j ↦ (c j : ZMod q))-L := by
    convert dvd_sub hd' hred using 1
    ring
  have hL : L.degree < n := by
    apply (degree_sub_le _ _).trans_lt
    apply max_lt
    · exact (degree_C_le : degree (C (A : ZMod q)) ≤ (0 : WithBot ℕ)).trans_lt (WithBot.coe_lt_coe.mpr (NeZero.pos n))
    · exact (degree_C_mul_X_le _).trans_lt (WithBot.coe_lt_coe.mpr hn)
  have hz := eq_zero_of_dvd_of_degree_lt hdiff (by
    dsimp [f]
    rw [degree_X_pow_sub_C (NeZero.pos n)]
    exact (degree_sub_le _ _).trans_lt (max_lt (reduced_degree_lt _ _ _) hL))
  exact sub_eq_zero.mp hz

lemma product_val (q : ℕ) (j : ZMod n) :
    (j*(q : ZMod n)).val=j.val*q%n := by
  have h : ((j.val*q : ℕ) : ZMod n)=j*(q : ZMod n) := by simp
  rw [← h,ZMod.val_natCast]

/-- Coprimality makes the reduced monomials occupy distinct coefficient positions. -/
lemma reduced_coeff (q : ℕ) (hq : q.Coprime n) (k : ZMod q) (c : ZMod n → ZMod q)
    (j : ZMod n) : (reduced q k c).coeff (j.val*q%n)=c j*k^(j.val*q/n) := by
  classical
  have hinj : Function.Injective (fun t : ZMod n ↦ t.val*q%n) := by
    intro t v h
    apply ((ZMod.isUnit_iff_coprime q n).mpr hq).mul_right_cancel
    apply ZMod.val_injective
    simpa only [product_val] using h
  simp only [reduced,finsetSum_coeff,coeff_C_mul_X_pow]
  simp_rw [hinj.eq_iff]
  simp

/-- Away from the two distinguished residues, the coefficients vanish modulo q. -/
theorem coefficient_cast_eq_zero (q : ℕ) [Fact q.Prime] (hn : 1<n) (hq : q.Coprime n)
    (k A s : ℤ) (hk : (k : ZMod q)≠0) (c : ZMod n → ℤ)
    (hd : pureBinomial n k ∣ (coefficientPolynomial c)^q-C A+C s*X)
    (j : ZMod n) (hj : j≠0) (hjq : j*(q : ZMod n)≠1) : (c j : ZMod q)=0 := by
  have hzero : j.val*q%n≠0 := by
    intro h
    apply hj
    apply ((ZMod.isUnit_iff_coprime q n).mpr hq).mul_right_cancel
    apply ZMod.val_injective
    simpa [product_val] using h
  have hone : j.val*q%n≠1 := by
    intro h
    apply hjq
    apply ZMod.val_injective
    rw [product_val,h]
    symm
    exact ZMod.val_one'' (by omega)
  have hh := congrArg (fun p : (ZMod q)[X] ↦ p.coeff (j.val*q%n))
    (reduced_relation q hn k A s c hd)
  rw [reduced_coeff q hq] at hh
  simp only [coeff_sub,coeff_C,coeff_C_mul_X,hzero,hone,ite_false,sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ hk)

/-- If q divides k and q>n, Frobenius is constant modulo X^n, already a contradiction. -/
theorem no_relation_of_cast_k_zero (q : ℕ) [Fact q.Prime] (hn : 1<n) (hnq : n<q)
    (k A s : ℤ) (hk : (k : ZMod q)=0) (hs : s=1 ∨ s= -1) (c : ZMod n → ℤ)
    (hd : pureBinomial n k ∣ (coefficientPolynomial c)^q-C A+C s*X) : False := by
  have hcoeff : (reduced q (0 : ZMod q) (fun j ↦ (c j : ZMod q))).coeff 1=0 := by
    simp only [reduced,finsetSum_coeff,coeff_C_mul_X_pow]
    apply sum_eq_zero
    intro j _
    by_cases hj : j.val=0
    · simp [hj]
    · have hm : n≤j.val*q := by
        have hh : q≤j.val*q := by simpa using Nat.mul_le_mul_right q (Nat.one_le_iff_ne_zero.mpr hj)
        omega
      have hd : 0<j.val*q/n := Nat.div_pos hm (NeZero.pos n)
      simp [zero_pow hd.ne']
  have hh := congrArg (fun p : (ZMod q)[X] ↦ p.coeff 1)
    (reduced_relation q hn k A s c hd)
  rw [hk,hcoeff] at hh
  simp only [coeff_sub,coeff_C,one_ne_zero,ite_false,coeff_C_mul_X,ite_true,zero_sub] at hh
  rcases hs with rfl | rfl <;> simp at hh

end PillaiFrobenius
