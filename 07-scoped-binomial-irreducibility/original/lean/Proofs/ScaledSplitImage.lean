import GeometricFiberProduct

/-! Unit-scaled split evaluations and reduced-degree polynomial representatives. -/
set_option autoImplicit false
open Polynomial
namespace PillaiFiber
universe u
variable {R : Type u} [CommRing R]

noncomputable def scalePolynomial (b : Rˣ) : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (C (b : R)*X) (C (↑(b⁻¹) : R)*X)
    (by simp [mul_comp,← C_mul,← mul_assoc])
    (by simp [mul_comp,← C_mul,← mul_assoc])

@[simp] lemma scalePolynomial_apply (b : Rˣ) (P : R[X]) :
    scalePolynomial b P=P.comp (C (b : R)*X) := rfl

noncomputable def scaledPair (n : ℕ) (b : Rˣ) : R[X] →+* R × AdjoinRoot (geometric (R := R) n) :=
  (polynomialPair (geometric n) 1).comp (scalePolynomial b).toRingHom

@[simp] lemma scaledPair_apply (n : ℕ) (b : Rˣ) (P : R[X]) :
    scaledPair n b P=(P.eval (b : R),AdjoinRoot.mk (geometric n) (P.comp (C (b : R)*X))) := by
  change polynomialPair (geometric n) 1 (scalePolynomial b P)=_
  simp only [scalePolynomial_apply,polynomialPair_apply,eval_comp,eval_mul,eval_C,eval_X,mul_one]

/-- Scaling by a unit preserves the exact compatible-residue image. -/
theorem scaledPair_image (n : ℕ) (b : Rˣ) (x : R) (y : AdjoinRoot (geometric (R := R) n)) :
    (∃ P,scaledPair n b P=(x,y)) ↔
      Ideal.Quotient.mk (Ideal.span {(n : R)}) x=geometricResidue n y := by
  rw [← splitPair_image]
  constructor
  · rintro ⟨P,hP⟩
    exact ⟨AdjoinRoot.mk ((X : R[X])^n-1) (scalePolynomial b P),hP⟩
  · rintro ⟨z,hz⟩
    obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective z
    refine ⟨(scalePolynomial b).symm Q,?_⟩
    change polynomialPair (geometric n) 1 (scalePolynomial b ((scalePolynomial b).symm Q))=(x,y)
    rw [AlgEquiv.apply_symm_apply]
    exact hz

lemma scalePolynomial_natDegree [IsDomain R] (b : Rˣ) (P : R[X]) :
    (scalePolynomial b P).natDegree=P.natDegree := by
  rw [scalePolynomial_apply,natDegree_comp,natDegree_C_mul_X _ b.ne_zero,mul_one]

/-- The scaled image has a representative of degree less than n. -/
theorem scaledPair_representative [IsDomain R] (n : ℕ) (hn : 0<n) (b : Rˣ)
    (x : R) (y : AdjoinRoot (geometric (R := R) n))
    (hxy : Ideal.Quotient.mk (Ideal.span {(n : R)}) x=geometricResidue n y) :
    ∃ P : R[X],P.natDegree<n ∧ P.eval (b : R)=x ∧
      AdjoinRoot.mk (geometric n) (P.comp (C (b : R)*X))=y := by
  obtain ⟨Q,hQ,hx,hy⟩ := splitPair_representative n hn x y hxy
  let P := (scalePolynomial b).symm Q
  have hscale : scalePolynomial b P=Q := (scalePolynomial b).apply_symm_apply Q
  have hnat : P.natDegree=Q.natDegree := by rw [← scalePolynomial_natDegree b P,hscale]
  have hp : scaledPair n b P=(x,y) := by
    change polynomialPair (geometric n) 1 (scalePolynomial b P)=(x,y)
    rw [hscale]
    exact Prod.ext hx hy
  rw [scaledPair_apply] at hp
  refine ⟨P,hnat ▸ hQ,?_,?_⟩
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

/-- The two unit-scaled evaluations determine every polynomial of degree below n. -/
theorem scaled_evaluation_unique [IsDomain R] (n : ℕ) (hn : (n : R)≠0) (b : Rˣ)
    (P Q : R[X]) (hP : P.natDegree<n) (hQ : Q.natDegree<n)
    (hx : P.eval (b : R)=Q.eval (b : R))
    (hy : AdjoinRoot.mk (geometric n) (P.comp (C (b : R)*X))=
      AdjoinRoot.mk (geometric n) (Q.comp (C (b : R)*X))) : P=Q := by
  apply (scalePolynomial b).injective
  apply split_evaluation_unique n hn
  · simpa only [scalePolynomial_natDegree] using hP
  · simpa only [scalePolynomial_natDegree] using hQ
  · simpa only [scalePolynomial_apply,eval_comp,eval_mul,eval_C,eval_X,mul_one] using hx
  · exact hy

/-- Root closure of the scaled polynomial image with no component-unit restriction. -/
theorem scaledPair_power_closed (n q : ℕ) (b : Rˣ)
    (hinj : Function.Injective (fun t : R ⧸ Ideal.span {(n : R)} ↦ t^q))
    (x : R) (y : AdjoinRoot (geometric (R := R) n))
    (hpow : ∃ P,scaledPair n b P=(x^q,y^q)) : ∃ P,scaledPair n b P=(x,y) := by
  apply (scaledPair_image n b x y).mpr
  apply hinj
  simpa only [map_pow] using (scaledPair_image n b (x^q) (y^q)).mp hpow

/-- The second scaled coordinate is literally evaluation at b times the adjoined root. -/
lemma scaled_root_evaluation (n : ℕ) (b : Rˣ) (P : R[X]) :
    aeval ((algebraMap R (AdjoinRoot (geometric n))) (b : R)*AdjoinRoot.root (geometric n)) P=
      AdjoinRoot.mk (geometric n) (P.comp (C (b : R)*X)) := by
  rw [← AdjoinRoot.aeval_eq,aeval_comp]
  simp only [map_mul,aeval_C,aeval_X]

end PillaiFiber
