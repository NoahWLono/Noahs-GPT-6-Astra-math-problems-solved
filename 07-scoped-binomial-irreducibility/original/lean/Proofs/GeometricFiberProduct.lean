import PolynomialFiberProduct
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic

/-! The geometric-sum split image and power injectivity on the full prime residue field. -/
set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace PillaiFiber
universe u
variable {R : Type u} [CommRing R]

noncomputable def geometric (n : ℕ) : R[X] := ∑ i ∈ Finset.range n,X^i

@[simp] theorem geometric_eval_one (n : ℕ) : (geometric (R := R) n).eval 1=(n : R) := by
  simp [geometric]

lemma geometric_relation (n : ℕ) : (X-C (1 : R))*geometric n=X^n-1 := by
  simpa only [C_1,geometric] using mul_geom_sum (X : R[X]) n

noncomputable def geometricResidue (n : ℕ) :
    AdjoinRoot (geometric (R := R) n) →+* R ⧸ Ideal.span {(n : R)} :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) (Ideal.Quotient.mk _ (1 : R)) (by
    rw [eval₂_at_apply,geometric_eval_one]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] lemma geometricResidue_mk (n : ℕ) (P : R[X]) :
    geometricResidue n (AdjoinRoot.mk (geometric n) P)=
      Ideal.Quotient.mk (Ideal.span {(n : R)}) (P.eval 1) := by
  rw [geometricResidue,AdjoinRoot.lift_mk,eval₂_at_apply]

/-- Actual evaluation map from R[T]/(T^n−1) to R × R[T]/(1+T+...+T^(n−1)). -/
noncomputable def splitPair (n : ℕ) :
    AdjoinRoot ((X : R[X])^n-1) →+* R × AdjoinRoot (geometric (R := R) n) :=
  Ideal.Quotient.lift _ (polynomialPair (geometric n) 1) (by
    intro P hP
    obtain ⟨Q,rfl⟩ := Ideal.mem_span_singleton.mp hP
    rw [map_mul,← geometric_relation,polynomialPair_relation,zero_mul])

@[simp] lemma splitPair_mk (n : ℕ) (P : R[X]) :
    splitPair n (AdjoinRoot.mk ((X : R[X])^n-1) P)=
      (P.eval 1,AdjoinRoot.mk (geometric n) P) := rfl

/-- The image consists exactly of pairs whose residues agree modulo n. -/
theorem splitPair_image (n : ℕ) (x : R) (y : AdjoinRoot (geometric (R := R) n)) :
    (∃ z,splitPair n z=(x,y)) ↔
      Ideal.Quotient.mk (Ideal.span {(n : R)}) x=geometricResidue n y := by
  have hh : (∃ z,splitPair n z=(x,y)) ↔ ∃ P,polynomialPair (geometric n) 1 P=(x,y) := by
    constructor
    · rintro ⟨z,hz⟩
      obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective z
      exact ⟨P,hz⟩
    · rintro ⟨P,hP⟩
      exact ⟨AdjoinRoot.mk _ P,hP⟩
  rw [hh,polynomialPair_image]
  obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective y
  rw [residueHom_mk,geometricResidue_mk,Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem,geometric_eval_one]

/-- No nonzero residue characteristic can collapse the quotient evaluation map in a domain. -/
theorem splitPair_injective [IsDomain R] (n : ℕ) (hn : (n : R)≠0) :
    Function.Injective (splitPair (R := R) n) := by
  intro x y hxy
  obtain ⟨P,rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  rw [← geometric_relation]
  apply (polynomialPair_eq_zero_iff (geometric n) 1 (by simpa using hn) (P-Q)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- The split image is closed under taking q-th roots when the residue power map is injective. -/
theorem splitPair_power_closed (n q : ℕ)
    (hinj : Function.Injective (fun t : R ⧸ Ideal.span {(n : R)} ↦ t^q))
    (x : R) (y : AdjoinRoot (geometric (R := R) n))
    (hpow : ∃ z,splitPair n z=(x^q,y^q)) : ∃ z,splitPair n z=(x,y) := by
  apply (splitPair_image n x y).mpr
  apply hinj
  simpa only [map_pow] using (splitPair_image n (x^q) (y^q)).mp hpow

/-- Power injectivity on all of F_p, including zero; no nonzero-residue assumption. -/
theorem zmod_power_injective (p q : ℕ) [Fact p.Prime] (hq : 0<q)
    (hc : Nat.Coprime (p-1) q) : Function.Injective (fun t : ZMod p ↦ t^q) := by
  intro x y hxy
  by_cases hx : x=0
  · subst x
    simpa only [zero_pow (Nat.ne_of_gt hq),eq_comm,pow_eq_zero_iff (Nat.ne_of_gt hq)] using hxy
  by_cases hy : y=0
  · subst y
    simpa only [zero_pow (Nat.ne_of_gt hq),pow_eq_zero_iff (Nat.ne_of_gt hq)] using hxy
  have hu : Nat.Coprime (Nat.card (ZMod p)ˣ) q := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hc
  have hh : (Units.mk0 x hx)^q=(Units.mk0 y hy)^q := Units.ext hxy
  have he := hu.pow_left_bijective.injective hh
  exact congrArg Units.val he

/-- Compatible pairs have an actual polynomial representative of degree less than n. -/
theorem splitPair_representative [Nontrivial R] (n : ℕ) (hn : 0<n)
    (x : R) (y : AdjoinRoot (geometric (R := R) n))
    (hxy : Ideal.Quotient.mk (Ideal.span {(n : R)}) x=geometricResidue n y) :
    ∃ P : R[X],P.natDegree<n ∧ P.eval 1=x ∧ AdjoinRoot.mk (geometric n) P=y := by
  obtain ⟨z,hz⟩ := (splitPair_image n x y).mpr hxy
  obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective z
  let F : R[X] := X^n-1
  have hmon : F.Monic := by
    simpa only [F,C_1] using monic_X_pow_sub_C (1 : R) (Nat.ne_of_gt hn)
  have hdeg : F.natDegree=n := by
    simpa only [F,C_1] using (natDegree_X_pow_sub_C (n := n) (r := (1 : R)))
  have hne : F≠1 := by
    intro hh
    have := congrArg natDegree hh
    rw [hdeg,natDegree_one] at this
    omega
  have hmk := AdjoinRoot.mk_leftInverse hmon (AdjoinRoot.mk F Q)
  change AdjoinRoot.mk F (Q %ₘ F)=AdjoinRoot.mk F Q at hmk
  have heq := congrArg (splitPair (R := R) n) hmk
  rw [hz] at heq
  refine ⟨Q %ₘ F,?_,congrArg Prod.fst heq,congrArg Prod.snd heq⟩
  simpa only [hdeg] using natDegree_modByMonic_lt Q hmon hne

/-- Equality of both evaluations determines a polynomial in the reduced degree range. -/
theorem split_evaluation_unique [IsDomain R] (n : ℕ) (hn : (n : R)≠0)
    (P Q : R[X]) (hP : P.natDegree<n) (hQ : Q.natDegree<n)
    (hx : P.eval 1=Q.eval 1)
    (hy : AdjoinRoot.mk (geometric n) P=AdjoinRoot.mk (geometric n) Q) : P=Q := by
  have hh : polynomialPair (geometric n) 1 P=polynomialPair (geometric n) 1 Q := Prod.ext hx hy
  have hd : (X-C (1 : R))*geometric n∣P-Q :=
    (polynomialPair_eq_zero_iff _ _ (by simpa using hn) _).mp (by rw [map_sub,hh,sub_self])
  rw [geometric_relation] at hd
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hd
  have hdeg : ((X : R[X])^n-1).natDegree=n := by
    simpa only [C_1] using (natDegree_X_pow_sub_C (n := n) (r := (1 : R)))
  rw [hdeg]
  exact (natDegree_sub_le P Q).trans_lt (max_lt hP hQ)

end PillaiFiber
