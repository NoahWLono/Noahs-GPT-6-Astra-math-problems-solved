import FamilyAlgebra.UniformFamily

namespace FamilyAlgebra
open FastWalsh QuadraticWalshShift QuadraticWalshMatrix

/-- The same binary affine law used by the concrete finite certificate. -/
def IsAffine {n m : Nat} (f : BitVec n → BitVec m) : Prop :=
  ∀ x y, f (x ^^^ y) = (f x ^^^ f y ^^^ f 0)

/-- A squarefree homogeneous quadratic representation with valid indices. -/
def IsHomogeneousQuadratic {n m : Nat} (f : BitVec n → BitVec m) : Prop :=
  ∃ cs : List (Nat × Nat × BitVec m),
    (∀ c ∈ cs, c.1<c.2.1 ∧ c.2.1<n) ∧ f=quadratic cs

theorem familyCoefficients_valid (L : V m →ₗ[ZMod 2] QuadraticWalshFamily.Bilin n) :
    ∀ c ∈ QuadraticWalshFamily.familyCoefficients L, c.1<c.2.1 ∧ c.2.1<n := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨p,hp,rfl⟩
  have hp' := Finset.mem_filter.mp (Finset.mem_toList.mp hp)
  exact ⟨hp'.2,p.2.isLt⟩

theorem quadratic_at_zero (cs : List (Nat × Nat × BitVec m)) :
    quadratic cs (0 : BitVec n)=0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (if (0 : BitVec n).getLsbD c.1 && (0 : BitVec n).getLsbD c.2.1 then c.2.2 else 0) ^^^ quadratic cs (0 : BitVec n) = 0
    rw [ih]
    simp

theorem affine_quadratic_polar_zero (cs : List (Nat × Nat × BitVec m))
    (ha : IsAffine (quadratic cs : BitVec n → BitVec m)) (b : BitVec m) (a x : BitVec n) :
    coefficientPolar cs b a x=false := by
  have hc := congrArg (binaryDot b) (ha x a)
  rw [quadratic_at_zero] at hc
  have hc' : quadraticComponent cs b (x ^^^ a) =
      (quadraticComponent cs b x ^^ quadraticComponent cs b a) := by
    simpa only [binaryDot_xor_right, binaryDot_zero, Bool.xor_false,
      quadratic_component_correct] using hc
  have ht := quadraticComponent_translate cs b a x
  rw [hc'] at ht
  have cancel : ∀ p q r : Bool, (p ^^ q)=(p ^^ q ^^ r) → r=false := by decide
  exact cancel _ _ _ ht

/-- An actual bent component forces a quadratic vectorial map to be nonaffine
in every positive input dimension. -/
theorem bent_component_nonaffine (cs : List (Nat × Nat × BitVec m)) (positive : 0<n)
    (b : BitVec m) (hb : IsBent (quadratic cs : BitVec n → BitVec m) b) :
    ¬IsAffine (quadratic cs : BitVec n → BitVec m) := by
  intro ha
  have hn := (bent_iff_polarForm_nondegenerate cs b).mp hb
  have hz : ∀ v w : V n, polarForm cs b v w=0 := by
    intro v w
    change bitF (coefficientPolar cs b (decode v) (decode w))=0
    rw [affine_quadratic_polar_zero cs ha]
    rfl
  have hunit := hn (Pi.single ⟨0,positive⟩ 1) (hz _)
  have hvalue := congrFun hunit ⟨0,positive⟩
  simp at hvalue

def goodCoordinates (e : Nat) : Fin (4*e) → ZMod 2 := fun i => if i.val=0 then 1 else 0

theorem goodCoordinates_not_bad (e : Nat) (positive : 0<e) :
    ¬badFullMask e positive (goodCoordinates e) := by
  have h0 : 0<2*e+2 := by omega
  have h1 : 1<2*e+2 := by omega
  have h2 : 2<2*e+2 := by omega
  have h3 : 3<2*e+2 := by omega
  simp [badFullMask, badParameters, paramRead, projectParameters,
    goodCoordinates, h0,h1,h2,h3,f2Bit,sixBaseTuples]

/-- Strengthened final theorem: one squarefree homogeneous quadratic map,
explicitly nonaffine, with the exact actual-Walsh nonbent component count. -/
theorem uniform_nonaffine_quadratic (e : Nat) (positive : 0<e) :
    ∃ f : BitVec (4*e) → BitVec (4*e),
      IsHomogeneousQuadratic f ∧ ¬IsAffine f ∧
      Nat.card {b : BitVec (4*e) // ¬IsBent f b ∧ b≠0}=3*2^(2*e-1)-1 := by
  classical
  obtain ⟨a,ha⟩ := galois_power_basis e positive
  let L := fullLinearFamily e positive a
  let cs := QuadraticWalshFamily.familyCoefficients L
  have hAlt : ∀ t v, L t v v=0 := fun t => fullLinearFamily_alt e positive a t
  have hclass : ∀ b : BitVec (4*e), IsBent (quadratic cs : BitVec (4*e) → BitVec (4*e)) b ↔
      ¬badFullMask e positive (coords b) := by
    intro b
    rw [QuadraticWalshFamily.family_bent_iff L hAlt b]
    exact fullLinearFamily_nondegenerate_iff e positive a ha (coords b)
  have hgood : IsBent (quadratic cs : BitVec (4*e) → BitVec (4*e)) (decode (goodCoordinates e)) := by
    rw [hclass, coords_decode]
    exact goodCoordinates_not_bad e positive
  refine ⟨quadratic cs, ⟨cs, familyCoefficients_valid L, rfl⟩,
    bent_component_nonaffine cs (by omega) _ hgood, ?_⟩
  exact nonzero_nonbent_card_of_classification e positive (quadratic cs) hclass

#print axioms uniform_nonaffine_quadratic
end FamilyAlgebra
