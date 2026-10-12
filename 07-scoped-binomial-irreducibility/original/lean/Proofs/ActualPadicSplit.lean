import CanonicalPadicCyclotomic
import PadicSplitImage

/-! The split root-closure theorem transferred to the actual local cyclotomic field. -/
set_option autoImplicit false
open Algebra Polynomial
namespace PillaiCyclotomic

noncomputable def localIntegralEmbedding (p : ℕ) [Fact p.Prime] :
    AdjoinRoot (PillaiFiber.geometric (R := ℤ_[p]) p) →ₐ[ℤ_[p]] LocalField p :=
  (integralClosure ℤ_[p] (LocalField p)).val.comp (localIntegralEquiv p).toAlgHom

lemma localIntegralEmbedding_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (localIntegralEmbedding p) :=
  Subtype.val_injective.comp (localIntegralEquiv p).injective

@[simp] lemma localIntegralEmbedding_root (p : ℕ) [Fact p.Prime] :
    localIntegralEmbedding p (AdjoinRoot.root (PillaiFiber.geometric p))=zeta p :=
  localIntegralEquiv_root p

/-- An integral element in the actual cyclotomic field, together with its scalar component,
has a common integral polynomial representative after the two q-th power equations. -/
theorem actual_split_power_equation (p q : ℕ) [Fact p.Prime]
    (hq : q.Prime) (hpq : p<q) (b : ℤ_[p]ˣ) (A x : ℤ_[p]) (y : LocalField p)
    (hyInt : IsIntegral ℤ_[p] y) (hx : x^q=A-(b : ℤ_[p]))
    (hy : y^q=algebraMap ℤ_[p] _ A-algebraMap ℤ_[p] _ (b : ℤ_[p])*zeta p) :
    ∃ P : ℤ_[p][X],P.natDegree<p ∧ P.eval (b : ℤ_[p])=x ∧
      aeval (algebraMap ℤ_[p] _ (b : ℤ_[p])*zeta p) P=y := by
  let w := (localIntegralEquiv p).symm ⟨y,hyInt⟩
  have hw : localIntegralEmbedding p w=y := by
    change ((localIntegralEquiv p) ((localIntegralEquiv p).symm ⟨y,hyInt⟩) : LocalField p)=y
    rw [AlgEquiv.apply_symm_apply]
  have hwq : w^q=algebraMap ℤ_[p] _ A-
      algebraMap ℤ_[p] _ (b : ℤ_[p])*AdjoinRoot.root (PillaiFiber.geometric p) := by
    apply localIntegralEmbedding_injective p
    simpa only [map_pow,map_sub,map_mul,AlgHom.commutes,localIntegralEmbedding_root,hw] using hy
  obtain ⟨P,hP,hPx,hPy⟩ := PillaiFiber.padic_scaled_prime_power_equation p q hq hpq b A x w hx hwq
  refine ⟨P,hP,hPx,?_⟩
  have hh := congrArg (localIntegralEmbedding p) hPy
  rw [hw] at hh
  rw [← aeval_algHom_apply] at hh
  simpa only [map_mul,AlgHom.commutes,localIntegralEmbedding_root] using hh

/-- Minimal polynomial of the chosen primitive root over the actual p-adic field. -/
theorem zeta_minpoly_field (p : ℕ) [Fact p.Prime] :
    cyclotomic p ℚ_[p]=minpoly ℚ_[p] (zeta p) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p]
    (cyclotomic_root_integral p (zeta p) (zeta_aeval p)),
    ← cyclotomic_eq_minpoly p (zeta p) (zeta_aeval p),map_cyclotomic]

/-- Two actual field evaluations determine a p-adic polynomial of degree below p. -/
theorem actual_split_evaluation_unique (p : ℕ) [hp : Fact p.Prime] (b : ℚ_[p]ˣ)
    (P Q : ℚ_[p][X]) (hP : P.natDegree<p) (hQ : Q.natDegree<p)
    (hx : P.eval (b : ℚ_[p])=Q.eval (b : ℚ_[p]))
    (hy : aeval (algebraMap ℚ_[p] _ (b : ℚ_[p])*zeta p) P=
      aeval (algebraMap ℚ_[p] _ (b : ℚ_[p])*zeta p) Q) : P=Q := by
  apply PillaiFiber.scaled_evaluation_unique p (Nat.cast_ne_zero.mpr hp.out.ne_zero) b P Q hP hQ hx
  apply AdjoinRoot.mk_eq_mk.mpr
  rw [← sub_comp]
  have hg : PillaiFiber.geometric (R := ℚ_[p]) p=cyclotomic p ℚ_[p] :=
    (cyclotomic_prime ℚ_[p] p).symm
  rw [hg,zeta_minpoly_field]
  apply minpoly.dvd ℚ_[p] (zeta p)
  simpa only [aeval_comp,map_mul,aeval_C,aeval_X,map_sub,sub_eq_zero] using hy

end PillaiCyclotomic
