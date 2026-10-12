import ScaledSplitImage
import Mathlib.NumberTheory.Padics.RingHoms

/-! Concrete residue-field power closure for the geometric split image over p-adic integers. -/
set_option autoImplicit false
open Polynomial
namespace PillaiFiber

noncomputable def padicResidueEquiv (p : ℕ) [Fact p.Prime] :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq PadicInt.maximalIdeal_eq_span_p.symm).trans PadicInt.residueField

/-- The residue power map is proved injective via the actual p-adic residue isomorphism. -/
theorem padic_quotient_power_injective (p q : ℕ) [Fact p.Prime] (hq : 0<q)
    (hc : Nat.Coprime (p-1) q) :
    Function.Injective (fun t : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])} ↦ t^q) := by
  intro x y hxy
  apply (padicResidueEquiv p).injective
  apply zmod_power_injective p q hq hc
  simpa only [map_pow] using congrArg (padicResidueEquiv p) hxy

/-- Root closure of the actual Z_p polynomial quotient image, including nonunit components. -/
theorem padic_split_power_closed (p q : ℕ) [Fact p.Prime] (hq : 0<q)
    (hc : Nat.Coprime (p-1) q) (x : ℤ_[p])
    (y : AdjoinRoot (geometric (R := ℤ_[p]) p))
    (hpow : ∃ z,splitPair p z=(x^q,y^q)) : ∃ z,splitPair p z=(x,y) :=
  splitPair_power_closed p q (padic_quotient_power_injective p q hq hc) x y hpow

/-- The explicit quotient evaluation map over Z_p is injective. -/
theorem padic_split_injective (p : ℕ) [hp : Fact p.Prime] :
    Function.Injective (splitPair (R := ℤ_[p]) p) :=
  splitPair_injective p (Nat.cast_ne_zero.mpr hp.out.ne_zero)

/-- The prime-exponent version required by the large-degree application. -/
theorem padic_split_prime_power_closed (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hpq : p<q) (x : ℤ_[p])
    (y : AdjoinRoot (geometric (R := ℤ_[p]) p))
    (hpow : ∃ z,splitPair p z=(x^q,y^q)) : ∃ z,splitPair p z=(x,y) := by
  apply padic_split_power_closed p q hq.pos _ x y hpow
  apply Nat.Coprime.symm
  apply (hq.coprime_iff_not_dvd).mpr
  apply Nat.not_dvd_of_pos_of_lt
  · have hp : p.Prime := Fact.out
    have := hp.two_le
    omega
  · omega

/-- An actual pair of q-th power equations produces a common integral polynomial of degree <p.
This is a theorem about the explicit geometric polynomial quotient, before field instantiation. -/
theorem padic_scaled_power_equation (p q : ℕ) [hp : Fact p.Prime] (hq : 0<q)
    (hc : Nat.Coprime (p-1) q) (b : ℤ_[p]ˣ) (A x : ℤ_[p])
    (y : AdjoinRoot (geometric (R := ℤ_[p]) p))
    (hx : x^q=A-(b : ℤ_[p]))
    (hy : y^q=algebraMap ℤ_[p] _ A-
      algebraMap ℤ_[p] _ (b : ℤ_[p])*AdjoinRoot.root (geometric p)) :
    ∃ P : ℤ_[p][X],P.natDegree<p ∧ P.eval (b : ℤ_[p])=x ∧
      aeval (algebraMap ℤ_[p] _ (b : ℤ_[p])*AdjoinRoot.root (geometric p)) P=y := by
  have hpair : scaledPair p b (C A-X)=(x^q,y^q) := by
    rw [scaledPair_apply]
    apply Prod.ext
    · simpa only [eval_sub,eval_C,eval_X] using hx.symm
    · simpa only [sub_comp,C_comp,X_comp,map_sub,map_mul,AdjoinRoot.mk_C,AdjoinRoot.mk_X,AdjoinRoot.algebraMap_eq] using hy.symm
  have hres := (scaledPair_image p b (x^q) (y^q)).mp ⟨C A-X,hpair⟩
  have heq : Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}) x=geometricResidue p y := by
    apply padic_quotient_power_injective p q hq hc
    simpa only [map_pow] using hres
  obtain ⟨P,hP,hxP,hyP⟩ := scaledPair_representative p hp.out.pos b x y heq
  exact ⟨P,hP,hxP,(scaled_root_evaluation p b P).trans hyP⟩

/-- The prime-degree application of the concrete p-adic quotient theorem. -/
theorem padic_scaled_prime_power_equation (p q : ℕ) [hp : Fact p.Prime]
    (hq : q.Prime) (hpq : p<q) (b : ℤ_[p]ˣ) (A x : ℤ_[p])
    (y : AdjoinRoot (geometric (R := ℤ_[p]) p))
    (hx : x^q=A-(b : ℤ_[p]))
    (hy : y^q=algebraMap ℤ_[p] _ A-
      algebraMap ℤ_[p] _ (b : ℤ_[p])*AdjoinRoot.root (geometric p)) :
    ∃ P : ℤ_[p][X],P.natDegree<p ∧ P.eval (b : ℤ_[p])=x ∧
      aeval (algebraMap ℤ_[p] _ (b : ℤ_[p])*AdjoinRoot.root (geometric p)) P=y := by
  apply padic_scaled_power_equation p q hq.pos _ b A x y hx hy
  apply Nat.Coprime.symm
  apply (hq.coprime_iff_not_dvd).mpr
  exact Nat.not_dvd_of_pos_of_lt (by have := hp.out.two_le; omega) (by omega)

end PillaiFiber
