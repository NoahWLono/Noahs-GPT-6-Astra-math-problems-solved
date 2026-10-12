import PadicCyclotomicEisenstein
import GeometricFiberProduct

/-! Actual identification of the geometric quotient with an integral cyclotomic power order. -/
set_option autoImplicit false
open Algebra Polynomial
namespace PillaiCyclotomic
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
variable [IsScalarTower ℤ_[p] ℚ_[p] L]

omit [Algebra ℚ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
lemma cyclotomic_root_integral (ζ : L) (hζ : aeval ζ (cyclotomic p ℤ_[p])=0) :
    IsIntegral ℤ_[p] ζ := ⟨_,cyclotomic.monic p ℤ_[p],hζ⟩

theorem cyclotomic_eq_minpoly (ζ : L) (hζ : aeval ζ (cyclotomic p ℤ_[p])=0) :
    cyclotomic p ℤ_[p]=minpoly ℤ_[p] ζ :=
  PillaiEisenstein.monic_irreducible_eq_minpoly (K := ℚ_[p]) _
    (cyclotomic.monic p ℤ_[p]) (cyclotomic_irreducible p) ζ hζ

local instance : Module.IsTorsionFree ℤ_[p] L := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
  exact (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

/-- Explicit algebra equivalence from the proved geometric quotient model to the actual order. -/
noncomputable def orderEquiv (ζ : L) (hζ : aeval ζ (cyclotomic p ℤ_[p])=0) :
    AdjoinRoot (PillaiFiber.geometric (R := ℤ_[p]) p) ≃ₐ[ℤ_[p]] adjoin ℤ_[p] ({ζ} : Set L) :=
  (AdjoinRoot.algEquivOfEq ℤ_[p] _ _ (show PillaiFiber.geometric p=minpoly ℤ_[p] ζ from by
    rw [← cyclotomic_eq_minpoly p ζ hζ]
    simpa only [PillaiFiber.geometric] using (cyclotomic_prime ℤ_[p] p).symm)).trans
      (minpoly.equivAdjoin (cyclotomic_root_integral p ζ hζ))

/-- The equivalence sends the adjoined polynomial root to the chosen actual root. -/
theorem orderEquiv_root (ζ : L) (hζ : aeval ζ (cyclotomic p ℤ_[p])=0) :
    ((orderEquiv p ζ hζ) (AdjoinRoot.root (PillaiFiber.geometric p)) : L)=ζ := by
  simp only [orderEquiv,AlgEquiv.trans_apply,AdjoinRoot.algEquivOfEq_root,minpoly.coe_equivAdjoin]
  exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := ℤ_[p]) (x := ζ)

/-- A root of the shifted polynomial generates the full integral order after adding one. -/
theorem integralClosure_eq_cyclotomic_order (B : PowerBasis ℚ_[p] L)
    (hroot : aeval B.gen (shifted p ℤ_[p])=0) :
    integralClosure ℤ_[p] L=adjoin ℤ_[p] ({B.gen+1} : Set L) := by
  have hdeg : 0<(shifted p ℤ_[p]).natDegree := by
    rw [shifted_natDegree]
    have := hp.out.two_le
    omega
  rw [PillaiEisenstein.integralClosure_eq_adjoin_of_polynomial B (p : ℤ_[p])
    PadicInt.irreducible_p (shifted p ℤ_[p]) (shifted_monic p ℤ_[p]) hdeg
    (shifted_eisenstein p) hroot]
  apply le_antisymm
  · apply Algebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    have hh := (adjoin ℤ_[p] ({B.gen+1} : Set L)).sub_mem
      (self_mem_adjoin_singleton ℤ_[p] (B.gen+1)) (Subalgebra.one_mem _)
    convert hh using 1; simp only [add_sub_cancel_right,SetLike.mem_coe]
  · apply Algebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    exact Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ_[p] B.gen) (Subalgebra.one_mem _)

omit [IsScalarTower ℤ_[p] ℚ_[p] L] in
lemma shifted_root_add_one (B : PowerBasis ℚ_[p] L)
    (hroot : aeval B.gen (shifted p ℤ_[p])=0) :
    aeval (B.gen+1) (cyclotomic p ℤ_[p])=0 := by
  simpa only [shifted,aeval_comp,map_add,aeval_X,map_one] using hroot

/-- The quotient model is isomorphic to the actual integral closure, without an assumed
maximality or minimal-polynomial hypothesis. -/
noncomputable def integralClosureEquiv (B : PowerBasis ℚ_[p] L)
    (hroot : aeval B.gen (shifted p ℤ_[p])=0) :
    AdjoinRoot (PillaiFiber.geometric (R := ℤ_[p]) p) ≃ₐ[ℤ_[p]] integralClosure ℤ_[p] L :=
  (orderEquiv p (B.gen+1) (shifted_root_add_one p B hroot)).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_eq_cyclotomic_order p B hroot).symm)

theorem integralClosureEquiv_root (B : PowerBasis ℚ_[p] L)
    (hroot : aeval B.gen (shifted p ℤ_[p])=0) :
    (integralClosureEquiv p B hroot (AdjoinRoot.root (PillaiFiber.geometric p)) : L)=B.gen+1 := by
  exact orderEquiv_root p (B.gen+1) (shifted_root_add_one p B hroot)

end PillaiCyclotomic
