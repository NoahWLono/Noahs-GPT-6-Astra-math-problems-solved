import APNCoordinateLabels

set_option maxHeartbeats 300000

namespace APNRedo
open FastWalsh QuadraticWalshShift
open QuadraticWalshMatrix (coords decode bitF fBit)

/-- Encode the actual arbitrary quadratic map into the existing Walsh domain. -/
def encodedQuadratic (Q : QuadraticMap F (V n) (V n)) : BitVec n → BitVec n :=
  fun x => decode (Q (coords x))

@[simp] theorem encodedQuadratic_zero (Q : QuadraticMap F (V n) (V n)) :
    encodedQuadratic Q 0=0 := by
  unfold encodedQuadratic
  rw [QuadraticWalshMatrix.coords_zero,Q.map_zero,QuadraticWalshMatrix.decode_zero]

/-- Translation identity for the actual encoded quadratic map, including its
actual coordinate polar form. -/
theorem encodedQuadratic_translate (Q : QuadraticMap F (V n) (V n))
    (b x a : BitVec n) :
    binaryDot b (encodedQuadratic Q (x^^^a))=
      (binaryDot b (encodedQuadratic Q x) ^^ binaryDot b (encodedQuadratic Q a) ^^
        fBit (componentPencil Q (coords b) (coords a) (coords x))) := by
  apply QuadraticWalshMatrix.bitF_injective
  rw [QuadraticWalshMatrix.bitF_xor,QuadraticWalshMatrix.bitF_xor,
    QuadraticWalshMatrix.bitF_fBit]
  simp only [QuadraticWalshFamily.bitF_binaryDot,encodedQuadratic,
    QuadraticWalshMatrix.coords_decode,QuadraticWalshMatrix.coords_xor,componentPencil_apply]
  rw [QuadraticMap.map_add Q, dotProduct_add,dotProduct_add]
  congr 1
  rw [QuadraticMap.polar_comm Q]
  rfl

/-- Nonsingularity gives actual Walsh bentness by solving for each linear phase,
then applying the existing independently checked Parseval identity. -/
theorem encodedQuadratic_bent_of_nondegenerate
    (Q : QuadraticMap F (V n) (V n)) (b : BitVec n)
    (hB : Nondegenerate (componentPencil Q (coords b))) : IsBent (encodedQuadratic Q) b := by
  let B := componentPencil Q (coords b)
  have hs : ∀u:BitVec n, ∃a:BitVec n, ∀x,
      binaryDot b (encodedQuadratic Q (x^^^a))=
        (binaryDot b (encodedQuadratic Q x) ^^ binaryDot b (encodedQuadratic Q a) ^^ binaryDot u x) := by
    intro u
    let v := (formEquiv B hB).symm (coordinateDotForm n (coords u))
    refine ⟨decode v,?_⟩
    intro x
    rw [encodedQuadratic_translate]
    congr 1
    apply QuadraticWalshMatrix.bitF_injective
    rw [QuadraticWalshMatrix.bitF_fBit,QuadraticWalshFamily.bitF_binaryDot,
      QuadraticWalshMatrix.coords_decode]
    have hh := (formEquiv B hB).apply_symm_apply (coordinateDotForm n (coords u))
    exact LinearMap.congr_fun hh (coords x)
  have hconst : ∀u:BitVec n,
      walsh (encodedQuadratic Q) b u*walsh (encodedQuadratic Q) b u=
        walsh (encodedQuadratic Q) b 0*walsh (encodedQuadratic Q) b 0 := by
    intro u
    obtain ⟨a,ha⟩ := hs u
    rw [walsh_shift (encodedQuadratic Q) b u a ha]
    cases binaryDot b (encodedQuadratic Q a) <;> simp [signed,Int.neg_mul_neg]
  have hp := QuadraticWalshParseval.walsh_parseval (encodedQuadratic Q) b
  simp only [hconst,QuadraticWalshParseval.sumDomain_const] at hp
  have hn : (↑(2^n:Nat):Int)≠0 := by
    have h : 0<(2^n:Nat) := Nat.pow_pos (by decide)
    omega
  have hz := Int.eq_of_mul_eq_mul_left hn hp
  intro u
  exact (hconst u).trans hz

/-- A genuine nonzero radical yields an actual zero Walsh coefficient. -/
theorem encodedQuadratic_not_bent_of_degenerate
    (Q : QuadraticMap F (V n) (V n)) (b : BitVec n)
    (hB : ¬Nondegenerate (componentPencil Q (coords b))) : ¬IsBent (encodedQuadratic Q) b := by
  classical
  simp only [Nondegenerate,not_forall] at hB
  obtain ⟨v,hv⟩ := hB
  have hv0 : v≠0 := by tauto
  have hrad : ∀x, componentPencil Q (coords b) v x=0 := by tauto
  let a := decode v
  have ha0 : a≠0 := by
    intro he
    have hh := congrArg coords he
    exact hv0 (by simpa only [a,QuadraticWalshMatrix.coords_decode,
      QuadraticWalshMatrix.coords_zero] using hh)
  let q := fun x => binaryDot b (encodedQuadratic Q x)
  have htrans : ∀x, q (x^^^a)=(q x ^^ q a) := by
    intro x
    dsimp only [q]
    rw [encodedQuadratic_translate]
    simp only [a,QuadraticWalshMatrix.coords_decode,hrad,QuadraticWalshMatrix.fBit,
      ne_eq,not_true_eq_false,decide_false,Bool.xor_false]
  have hex : ∃u:BitVec n, (q a ^^ binaryDot u a)=true := by
    cases hqa : q a
    · obtain ⟨u,hu⟩ := QuadraticWalshRadical.binaryDot_detect a ha0
      exact ⟨u,by simp only [hqa,Bool.false_xor,hu]⟩
    · exact ⟨0,by simp only [hqa,binaryDot_zero_left,Bool.xor_false]⟩
  obtain ⟨u,hu⟩ := hex
  have hw := QuadraticWalshRadical.booleanWalsh_zero_of_translation q a u htrans hu
  intro hb
  have hh := hb u
  rw [walsh_eq_booleanWalsh] at hh
  change booleanWalsh q u*booleanWalsh q u=↑(2^n:Nat) at hh
  rw [hw] at hh
  have hp : 0<(2^n:Nat) := Nat.pow_pos (by decide)
  omega

theorem encodedQuadratic_bent_iff (Q : QuadraticMap F (V n) (V n)) (b : BitVec n) :
    IsBent (encodedQuadratic Q) b ↔ Nondegenerate (componentPencil Q (coords b)) := by
  constructor
  · intro hb
    by_contra hn
    exact encodedQuadratic_not_bent_of_degenerate Q b hn hb
  · exact encodedQuadratic_bent_of_nondegenerate Q b

/-- Adding a fixed output changes an actual Walsh coefficient only by its sign. -/
theorem walsh_output_xor_constant (f : BitVec n → BitVec m) (c b : BitVec m) (u : BitVec n) :
    walsh (fun x => f x^^^c) b u=signed (binaryDot b c) (walsh f b u) := by
  rw [walsh_eq_booleanWalsh,walsh_eq_booleanWalsh]
  unfold booleanWalsh
  rw [←sumDomain_signed]
  apply congrArg sumDomain
  funext x
  dsimp only
  rw [binaryDot_xor_right]
  cases binaryDot b (f x) <;> cases binaryDot b c <;> cases binaryDot u x <;> decide

theorem bent_output_xor_constant_iff (f : BitVec n → BitVec m) (c b : BitVec m) :
    IsBent (fun x => f x^^^c) b ↔ IsBent f b := by
  unfold IsBent
  simp only [walsh_output_xor_constant]
  cases binaryDot b c <;> simp [signed,Int.neg_mul_neg]

/-- Constants are included explicitly; linear terms are already permitted by
mathlib's characteristic-two QuadraticMap semantics. -/
def encodedQuadraticAffine (Q : QuadraticMap F (V n) (V n)) (c : V n) : BitVec n → BitVec n :=
  fun x => decode (Q (coords x)+c)

theorem encodedQuadraticAffine_bent_iff (Q : QuadraticMap F (V n) (V n))
    (c : V n) (b : BitVec n) :
    IsBent (encodedQuadraticAffine Q c) b ↔ Nondegenerate (componentPencil Q (coords b)) := by
  have he : encodedQuadraticAffine Q c=(fun x => encodedQuadratic Q x^^^decode c) := by
    funext x
    exact QuadraticWalshMatrix.decode_add _ _
  rw [he,bent_output_xor_constant_iff,encodedQuadratic_bent_iff]

#print axioms encodedQuadratic_bent_iff
#print axioms encodedQuadraticAffine_bent_iff
end APNRedo
