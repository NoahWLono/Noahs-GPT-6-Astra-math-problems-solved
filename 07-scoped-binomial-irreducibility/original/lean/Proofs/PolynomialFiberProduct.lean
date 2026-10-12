import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination

/-! Constructive polynomial evaluation fiber products with actual quotient residue maps. -/
set_option autoImplicit false
open Polynomial
namespace PillaiFiber
universe u
variable {R : Type u} [CommRing R]

noncomputable def residueHom (f : R[X]) (a : R) :
    AdjoinRoot f →+* R ⧸ Ideal.span {f.eval a} :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) (Ideal.Quotient.mk _ a) (by
    rw [eval₂_at_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] lemma residueHom_mk (f : R[X]) (a : R) (P : R[X]) :
    residueHom f a (AdjoinRoot.mk f P)=Ideal.Quotient.mk _ (P.eval a) := by
  rw [residueHom,AdjoinRoot.lift_mk,eval₂_at_apply]

noncomputable def polynomialPair (f : R[X]) (a : R) : R[X] →+* R × AdjoinRoot f :=
  (evalRingHom a).prod (AdjoinRoot.mk f)

@[simp] lemma polynomialPair_apply (f : R[X]) (a : R) (P : R[X]) :
    polynomialPair f a P=(P.eval a,AdjoinRoot.mk f P) := rfl

/-- Every compatible pair is represented by the explicit correction Q + c f. -/
theorem polynomialPair_image (f : R[X]) (a x : R) (y : AdjoinRoot f) :
    (∃ P : R[X],polynomialPair f a P=(x,y)) ↔
      Ideal.Quotient.mk (Ideal.span {f.eval a}) x=residueHom f a y := by
  constructor
  · rintro ⟨P,hP⟩
    have hx := congrArg Prod.fst hP
    have hy := congrArg Prod.snd hP
    change P.eval a=x at hx
    change AdjoinRoot.mk f P=y at hy
    rw [← hx,← hy,residueHom_mk]
  · intro hxy
    obtain ⟨Q,hQ⟩ := AdjoinRoot.mk_surjective y
    have hh : Ideal.Quotient.mk (Ideal.span {f.eval a}) (x-Q.eval a)=0 := by
      rw [map_sub,hxy,← hQ,residueHom_mk,sub_self]
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh)
    refine ⟨Q+C c*f,?_⟩
    apply Prod.ext
    · change (Q+C c*f).eval a=x
      simp only [eval_add,eval_mul,eval_C]
      linear_combination -hc
    · change AdjoinRoot.mk f (Q+C c*f)=y
      rw [map_add,map_mul,AdjoinRoot.mk_self,mul_zero,add_zero,hQ]

@[simp] lemma polynomialPair_relation (f : R[X]) (a : R) :
    polynomialPair f a ((X-C a)*f)=0 := by
  apply Prod.ext
  · change ((X-C a)*f).eval a=0
    simp only [eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul]
  · change AdjoinRoot.mk f ((X-C a)*f)=0
    rw [map_mul,AdjoinRoot.mk_self,mul_zero]

/-- The actual quotient map; its definition does not require a domain. -/
noncomputable def quotientPair (f : R[X]) (a : R) :
    AdjoinRoot ((X-C a)*f) →+* R × AdjoinRoot f :=
  Ideal.Quotient.lift _ (polynomialPair f a) (by
    intro P hP
    obtain ⟨Q,rfl⟩ := Ideal.mem_span_singleton.mp hP
    rw [map_mul,polynomialPair_relation,zero_mul])

@[simp] lemma quotientPair_mk (f : R[X]) (a : R) (P : R[X]) :
    quotientPair f a (AdjoinRoot.mk ((X-C a)*f) P)=polynomialPair f a P := rfl

/-- The explicit quotient map has exactly the compatible-residue image. -/
theorem quotientPair_image (f : R[X]) (a x : R) (y : AdjoinRoot f) :
    (∃ z,quotientPair f a z=(x,y)) ↔
      Ideal.Quotient.mk (Ideal.span {f.eval a}) x=residueHom f a y := by
  rw [← polynomialPair_image]
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective z
    exact ⟨P,hz⟩
  · rintro ⟨P,hP⟩
    exact ⟨AdjoinRoot.mk _ P,hP⟩

/-- Equal-residue root closure includes zero residues and requires only power injectivity
on the actual residue quotient. -/
theorem quotientPair_power_closed (f : R[X]) (a : R) (q : ℕ)
    (hinj : Function.Injective (fun t : R ⧸ Ideal.span {f.eval a} ↦ t^q))
    (x : R) (y : AdjoinRoot f) (hpow : ∃ z,quotientPair f a z=(x^q,y^q)) :
    ∃ z,quotientPair f a z=(x,y) := by
  apply (quotientPair_image f a x y).mpr
  apply hinj
  simpa only [map_pow] using (quotientPair_image f a (x^q) (y^q)).mp hpow

/-- The kernel is the product ideal once evaluation of f is a nonzero element of a domain. -/
theorem polynomialPair_eq_zero_iff [IsDomain R] (f : R[X]) (a : R)
    (hfa : f.eval a≠0) (P : R[X]) :
    polynomialPair f a P=0 ↔ (X-C a)*f∣P := by
  constructor
  · intro hP
    have hx := congrArg Prod.fst hP
    have hy := congrArg Prod.snd hP
    change P.eval a=0 at hx
    change AdjoinRoot.mk f P=0 at hy
    obtain ⟨Q,hQ⟩ := (AdjoinRoot.mk_eq_zero).mp hy
    rw [hQ,eval_mul] at hx
    have hQa : Q.eval a=0 := (mul_eq_zero.mp hx).resolve_left hfa
    obtain ⟨T,hT⟩ := (dvd_iff_isRoot).mpr hQa
    refine ⟨T,?_⟩
    rw [hQ,hT]
    ring
  · rintro ⟨Q,rfl⟩
    rw [map_mul,polynomialPair_relation,zero_mul]

/-- Injective realization of the polynomial quotient inside the product. -/
theorem quotientPair_injective [IsDomain R] (f : R[X]) (a : R) (hfa : f.eval a≠0) :
    Function.Injective (quotientPair f a) := by
  intro x y hxy
  obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  apply (polynomialPair_eq_zero_iff f a hfa (P-Q)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

end PillaiFiber
