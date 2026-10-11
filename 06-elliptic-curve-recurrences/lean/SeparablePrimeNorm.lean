/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
Reviewed adaptation from riemann-roch-function-fields commit
 dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
Changes: isolated local imports and existing reviewed divisor interface;
no external repository imports, build scripts, or metaprograms.
-/
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.FieldTheory.SeparableClosure

/-!
# Relative norms in finite separable extensions

Mathlib's theorem `Ideal.relNorm_eq_pow_of_isMaximal` assumes that the fraction field of the
base Dedekind domain is perfect.  For function fields the needed hypothesis is instead already
available in its sharp form: the particular fraction-field extension is separable.  This file
records that variant, using the same normal-closure argument as the Mathlib theorem.
-/



open Module
open UniqueFactorizationMonoid
open scoped nonZeroDivisors

namespace Ideal

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]

/-- The relative norm of a maximal ideal in a finite separable extension is the corresponding
prime below, raised to the inertia degree.  This is the separable-extension variant of
`Ideal.relNorm_eq_pow_of_isMaximal`. -/
theorem relNorm_eq_pow_of_isMaximal_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ P.inertiaDeg R := by
  let K := FractionRing R
  let L := FractionRing S
  letI : Algebra K L := FractionRing.liftAlgebra R L
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  letI : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  letI : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl
  let T : Type _ := integralClosure S E
  letI : Algebra S T := inferInstance
  letI : Algebra T E := inferInstance
  letI : IsScalarTower S T E := inferInstance
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R E := ((algebraMap S E).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
  letI : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 <| by
    rw [IsScalarTower.algebraMap_eq R S E]
    exact (algebraMap L E).injective.comp (IsFractionRing.injective S L) |>.comp
      (FaithfulSMul.algebraMap_injective R S)
  letI : IsScalarTower R S L := inferInstance
  letI : FaithfulSMul R L := inferInstance
  letI : IsScalarTower R L E := IsScalarTower.to₁₃₄ R S L E
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  letI : IsScalarTower R K E := IsScalarTower.to₁₂₄ R K L E
  letI : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  letI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).2 <| by
    intro x y hxy
    apply (algebraMap L E).injective.comp (IsFractionRing.injective S L)
    exact congrArg (fun z : T => (algebraMap T E) z) hxy
  letI : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).2 <| by
    rw [IsScalarTower.algebraMap_eq R S T]
    exact (FaithfulSMul.algebraMap_injective S T).comp
      (FaithfulSMul.algebraMap_injective R S)
  letI : FiniteDimensional K E :=
    normalClosure.is_finiteDimensional K L (AlgebraicClosure L)
  letI : Algebra.IsSeparable K E := by
    rw [← le_separableClosure_iff]
    apply normalClosure_le_iff.mpr
    intro i
    haveI : Algebra.IsSeparable K i.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i)
    exact le_separableClosure K (AlgebraicClosure L) i.fieldRange
  letI : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  letI : FiniteDimensional L E := Module.Finite.right K L E
  letI : IsFractionRing T E :=
    IsIntegralClosure.isFractionRing_of_finite_extension S L E T
  letI : Module.Finite S T := IsIntegralClosure.finite S L E T
  letI : Module.Finite R T := Module.Finite.trans S T
  letI : IsDedekindDomain T := integralClosure.isDedekindDomain S L E
  letI : IsGalois K E := {
    to_isSeparable := inferInstance
    to_normal := normalClosure.normal K L (AlgebraicClosure L) }
  let algT : Algebra T (FractionRing T) := inferInstance
  letI : Algebra T (FractionRing T) := algT
  letI : Algebra R (FractionRing T) := inferInstance
  letI : Algebra S (FractionRing T) := inferInstance
  letI : FaithfulSMul R (FractionRing T) := inferInstance
  letI : FaithfulSMul S (FractionRing T) := inferInstance
  letI : Algebra K (FractionRing T) := FractionRing.liftAlgebra R (FractionRing T)
  letI : Algebra L (FractionRing T) := FractionRing.liftAlgebra S (FractionRing T)
  letI : IsScalarTower R K (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing T)
  letI : IsScalarTower S L (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra S (FractionRing T)
  letI : IsGalois K (FractionRing T) := by
    refine IsGalois.of_equiv_equiv (F := K) (E := E)
      (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
      (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
    ext
    simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
      (FractionRing.algEquiv T E).symm _
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  letI : Q.IsMaximal := hQ₁
  letI : Q.LiesOver P := hQ₂
  letI : Q.LiesOver p := LiesOver.trans Q P p
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  letI : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    inertiaDeg_tower (R := R) P Q, pow_mul,
    pow_left_inj (inertiaDeg_pos Q S).ne'] at h


end Ideal
#print axioms Ideal.relNorm_eq_pow_of_isMaximal_of_isSeparable
