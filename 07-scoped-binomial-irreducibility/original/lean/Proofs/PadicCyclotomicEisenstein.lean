import MonicEisensteinClosure
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! Actual shifted cyclotomic Eisenstein and irreducibility theorems over Z_p and Q_p. -/
set_option autoImplicit false
open Polynomial
namespace PillaiCyclotomic

noncomputable def shifted (p : ℕ) (R : Type*) [CommRing R] : R[X] :=
  (cyclotomic p R).comp (X+1)

lemma shifted_monic (p : ℕ) (R : Type*) [CommRing R] : (shifted p R).Monic := by
  simpa only [shifted,C_1] using (cyclotomic.monic p R).comp_X_add_C (1 : R)

/-- Transport the actual Eisenstein coefficient divisibilities from Z to Z_p. -/
theorem map_integer_eisenstein (p : ℕ) [Fact p.Prime] (f : ℤ[X]) (hf : f.Monic)
    (he : f.IsEisensteinAt (Ideal.span {(p : ℤ)})) :
    (f.map (Int.castRingHom ℤ_[p])).IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) := by
  refine ⟨?_,?_,?_⟩
  · rw [(hf.map _).leadingCoeff,Ideal.mem_span_singleton]
    intro h
    exact PadicInt.p_nonunit (isUnit_iff_dvd_one.mpr h)
  · intro j hj
    rw [Ideal.mem_span_singleton,coeff_map]
    have hd := Ideal.mem_span_singleton.mp (he.mem (hj.trans_le natDegree_map_le))
    have hh := (PadicInt.pow_p_dvd_int_iff (p := p) 1 (f.coeff j)).mpr (by simpa using hd)
    simpa only [pow_one,Int.coe_castRingHom] using hh
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,coeff_map]
    have hd : ¬(p : ℤ)^2∣f.coeff 0 := by
      simpa only [Ideal.span_singleton_pow,Ideal.mem_span_singleton] using he.notMem
    exact (PadicInt.pow_p_dvd_int_iff (p := p) 2 (f.coeff 0)).not.mpr hd

/-- The actual shifted cyclotomic polynomial is Eisenstein over Z_p at (p). -/
theorem shifted_eisenstein (p : ℕ) [Fact p.Prime] :
    (shifted p ℤ_[p]).IsEisensteinAt (Ideal.span {(p : ℤ_[p])}) := by
  have he := map_integer_eisenstein p (shifted p ℤ) (shifted_monic p ℤ)
    (cyclotomic_comp_X_add_one_isEisensteinAt p)
  simpa only [shifted,map_comp,map_cyclotomic,Polynomial.map_add,map_X,Polynomial.map_one] using he

lemma shifted_natDegree (p : ℕ) [hp : Fact p.Prime] :
    (shifted p ℤ_[p]).natDegree=p-1 := by
  simp only [shifted,natDegree_comp,show (X+1 : ℤ_[p][X])=(X+C (1 : ℤ_[p])) by rw [C_1],
    natDegree_X_add_C,mul_one,natDegree_cyclotomic,Nat.totient_prime hp.out]

theorem shifted_irreducible (p : ℕ) [hp : Fact p.Prime] : Irreducible (shifted p ℤ_[p]) := by
  apply (shifted_eisenstein p).irreducible
  · rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  · exact (shifted_monic p ℤ_[p]).isPrimitive
  · rw [shifted_natDegree]
    have := hp.out.two_le
    omega

/-- Irreducibility over the actual p-adic fraction field. -/
theorem shifted_irreducible_field (p : ℕ) [Fact p.Prime] : Irreducible (shifted p ℚ_[p]) := by
  have hh := ((shifted_monic p ℤ_[p]).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[p])).mp (shifted_irreducible p)
  simpa only [shifted,map_comp,map_cyclotomic,Polynomial.map_add,map_X,Polynomial.map_one] using hh

/-- Undoing the translation proves irreducibility of the actual cyclotomic polynomial. -/
theorem cyclotomic_irreducible (p : ℕ) [Fact p.Prime] : Irreducible (cyclotomic p ℤ_[p]) := by
  have hh := shifted_irreducible p
  change Irreducible ((algEquivAevalXAddC (1 : ℤ_[p])) (cyclotomic p ℤ_[p])) at hh
  exact (MulEquiv.irreducible_iff (f := (algEquivAevalXAddC (1 : ℤ_[p])).toMulEquiv)).mp hh

end PillaiCyclotomic
