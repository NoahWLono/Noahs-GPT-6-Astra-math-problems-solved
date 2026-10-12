import PadicCyclotomicOrder

/-! A concrete cyclotomic field and its identified full integral order. -/
set_option autoImplicit false
open Algebra Polynomial
namespace PillaiCyclotomic

instance shifted_field_irreducible_fact (p : ℕ) [Fact p.Prime] :
    Fact (Irreducible (shifted p ℚ_[p])) := ⟨shifted_irreducible_field p⟩

/-- The actual field obtained by adjoining a root of Φ_p(T+1) to Q_p. -/
abbrev LocalField (p : ℕ) [Fact p.Prime] := AdjoinRoot (shifted p ℚ_[p])

noncomputable def localBasis (p : ℕ) [Fact p.Prime] : PowerBasis ℚ_[p] (LocalField p) :=
  AdjoinRoot.powerBasis (shifted_irreducible_field p).ne_zero

noncomputable def zeta (p : ℕ) [Fact p.Prime] : LocalField p := (localBasis p).gen+1

lemma localBasis_root (p : ℕ) [Fact p.Prime] :
    aeval (localBasis p).gen (shifted p ℤ_[p])=0 := by
  have hm : (shifted p ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])=shifted p ℚ_[p] := by
    simp only [shifted,map_comp,map_cyclotomic,Polynomial.map_add,map_X,Polynomial.map_one]
  have hh : aeval (localBasis p).gen ((shifted p ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p]))=0 := by
    rw [hm]
    change aeval (AdjoinRoot.root (shifted p ℚ_[p])) (shifted p ℚ_[p])=0
    rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self]
  simpa only [aeval_map_algebraMap] using hh

/-- The concrete cyclotomic field has its expected degree p−1. -/
theorem local_finrank (p : ℕ) [hp : Fact p.Prime] :
    Module.finrank ℚ_[p] (LocalField p)=p-1 := by
  rw [(localBasis p).finrank]
  change (shifted p ℚ_[p]).natDegree=p-1
  simp only [shifted,natDegree_comp,show (X+1 : ℚ_[p][X])=(X+C (1 : ℚ_[p])) by rw [C_1],
    natDegree_X_add_C,mul_one,natDegree_cyclotomic,Nat.totient_prime hp.out]

/-- The chosen zeta is an actual root of Φ_p. -/
lemma zeta_aeval (p : ℕ) [Fact p.Prime] :
    aeval (zeta p) (cyclotomic p ℤ_[p])=0 :=
  shifted_root_add_one p (localBasis p) (localBasis_root p)

/-- The concrete field's integral closure is exactly its cyclotomic power order. -/
theorem local_integralClosure (p : ℕ) [Fact p.Prime] :
    integralClosure ℤ_[p] (LocalField p)=adjoin ℤ_[p] ({zeta p} : Set (LocalField p)) :=
  integralClosure_eq_cyclotomic_order p (localBasis p) (localBasis_root p)

/-- Actual quotient-to-integral-closure identification for the concrete local field. -/
noncomputable def localIntegralEquiv (p : ℕ) [Fact p.Prime] :
    AdjoinRoot (PillaiFiber.geometric (R := ℤ_[p]) p) ≃ₐ[ℤ_[p]]
      integralClosure ℤ_[p] (LocalField p) :=
  integralClosureEquiv p (localBasis p) (localBasis_root p)

theorem localIntegralEquiv_root (p : ℕ) [Fact p.Prime] :
    (localIntegralEquiv p (AdjoinRoot.root (PillaiFiber.geometric p)) : LocalField p)=zeta p :=
  integralClosureEquiv_root p (localBasis p) (localBasis_root p)

/-- The chosen field element is a primitive p-th root of unity. -/
theorem zeta_primitive (p : ℕ) [hp : Fact p.Prime] : IsPrimitiveRoot (zeta p) p := by
  have hpQ : (p : ℚ_[p])≠0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  haveI : NeZero (p : LocalField p) := ⟨fun h ↦ hpQ ((algebraMap ℚ_[p] (LocalField p)).injective (by
    simpa only [map_natCast,map_zero] using h))⟩
  apply isRoot_cyclotomic_iff.mp
  rw [IsRoot,← map_cyclotomic p (algebraMap ℤ_[p] (LocalField p)),eval_map]
  exact zeta_aeval p

end PillaiCyclotomic
