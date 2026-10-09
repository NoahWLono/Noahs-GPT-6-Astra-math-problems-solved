import QuadraticWalshParseval
import QuadraticWalshRadical
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

namespace QuadraticWalshMatrix
open FastWalsh QuadraticWalshShift
abbrev F := ZMod 2
abbrev V (n : Nat) := Fin n → F

def bitF (b : Bool) : F := if b then 1 else 0
def fBit (z : F) : Bool := decide (z ≠ 0)

theorem fBit_bitF (b : Bool) : fBit (bitF b) = b := by cases b <;> decide
theorem bitF_fBit (z : F) : bitF (fBit z) = z := by fin_cases z <;> decide
theorem bitF_xor (a b : Bool) : bitF (a ^^ b) = bitF a + bitF b := by cases a <;> cases b <;> decide
theorem fBit_add (a b : F) : fBit (a+b) = (fBit a ^^ fBit b) := by fin_cases a <;> fin_cases b <;> decide

theorem bitF_injective : Function.Injective bitF := by
  intro a b h
  simpa only [fBit_bitF] using congrArg fBit h

def coords (a : BitVec n) : V n := fun i => bitF (a.getLsbD i)

def pack : {n : Nat} → (Fin n → Bool) → BitVec n
  | 0, _ => 0
  | n+1, f => BitVec.cons (f (Fin.last n)) (pack (fun i => f i.castSucc))

theorem pack_get (f : Fin n → Bool) (i : Fin n) : (pack f).getLsbD i = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [pack, Fin.val_last, BitVec.getLsbD_cons, if_pos rfl, ite_true]
    · simp only [pack, BitVec.getLsbD_cons]
      have hj : (j.castSucc : Fin (n+1)).val ≠ n := by exact Nat.ne_of_lt j.isLt
      simp only [hj, ↓reduceIte]
      exact ih _ j

def decode (v : V n) : BitVec n := pack (fun i => fBit (v i))

theorem coords_decode (v : V n) : coords (decode v) = v := by
  funext i
  simp only [coords, decode, pack_get, bitF_fBit]

theorem coords_injective : Function.Injective (@coords n) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bitF_injective (congrFun h ⟨i,hi⟩)

theorem decode_coords (a : BitVec n) : decode (coords a) = a :=
  coords_injective (coords_decode _)

theorem coords_zero : coords (0 : BitVec n) = 0 := by
  funext i
  simp [coords, bitF]

theorem coords_xor (a b : BitVec n) : coords (a ^^^ b) = coords a + coords b := by
  funext i
  simp only [coords, BitVec.getLsbD_xor, bitF_xor, Pi.add_apply]

theorem decode_zero : decode (0 : V n) = 0 := by
  apply coords_injective
  rw [coords_decode, coords_zero]

theorem decode_add (a b : V n) : decode (a+b) = (decode a ^^^ decode b) := by
  apply coords_injective
  rw [coords_decode, coords_xor, coords_decode, coords_decode]

def unitVec (i : Fin n) : BitVec n := decode (Pi.single i 1)

theorem coefficientPolar_zero_left (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (x : BitVec n) : coefficientPolar cs b 0 x = false := by
  have h := coefficientPolar_add_left cs b (0 : BitVec n) 0 x
  simpa using h

theorem coefficientPolar_zero_right (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (x : BitVec n) : coefficientPolar cs b x 0 = false := by
  rw [coefficientPolar_comm, coefficientPolar_zero_left]

/-- The actual polar functional in a completely explicit binary coordinate encoding. -/
def polarFunctional (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (a : BitVec n) : V n →ₗ[F] F where
  toFun v := bitF (coefficientPolar cs b a (decode v))
  map_add' x y := by rw [decode_add, coefficientPolar_add_right, bitF_xor]
  map_smul' c v := by
    fin_cases c
    · change bitF (coefficientPolar cs b a (decode (0 • v))) = (0 : F) • _
      rw [zero_smul, decode_zero, coefficientPolar_zero_right, zero_smul]
      rfl
    · change bitF (coefficientPolar cs b a (decode (1 • v))) = (1 : F) • _
      simp only [one_smul]

/-- The actual dot functional in those same coordinates. -/
def dotFunctional (u : BitVec n) : V n →ₗ[F] F where
  toFun v := bitF (binaryDot u (decode v))
  map_add' x y := by rw [decode_add, binaryDot_xor_right, bitF_xor]
  map_smul' c v := by
    fin_cases c
    · change bitF (binaryDot u (decode (0 • v))) = (0 : F) • _
      rw [zero_smul, decode_zero, binaryDot_zero, zero_smul]
      rfl
    · change bitF (binaryDot u (decode (1 • v))) = (1 : F) • _
      simp only [one_smul]

/-- Rows test against coordinate basis vectors; columns specify the radical input. -/
def polarLinear (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) : V n →ₗ[F] V n where
  toFun v i := bitF (coefficientPolar cs b (decode v) (unitVec i))
  map_add' v w := by ext i; simp only [decode_add, coefficientPolar_add_left, bitF_xor, Pi.add_apply]
  map_smul' c v := by
    fin_cases c
    · ext i
      change bitF (coefficientPolar cs b (decode (0 • v)) (unitVec i)) = (0 : F) • _
      rw [zero_smul, decode_zero, coefficientPolar_zero_left, zero_smul]
      rfl
    · ext i
      change bitF (coefficientPolar cs b (decode (1 • v)) (unitVec i)) = (1 : F) • _
      simp only [one_smul]

/-- This is the actual polar matrix, not an arbitrary matrix assumed to represent it. -/
def polarMatrix (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) : Matrix (Fin n) (Fin n) F :=
  LinearMap.toMatrix' (polarLinear cs b)

theorem polarMatrix_entry (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (i j : Fin n) : polarMatrix cs b i j = bitF (coefficientPolar cs b (unitVec j) (unitVec i)) := by
  rfl


theorem polarMatrix_mulVec (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (v : V n) : (polarMatrix cs b).mulVec v = polarLinear cs b v := by
  rw [← Matrix.toLin'_apply, polarMatrix, Matrix.toLin'_toMatrix']

/-- A binary-coordinate linear functional is determined by the actual unit vectors. -/
theorem functional_ext (f g : V n →ₗ[F] F)
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearMap.pi_ext
  intro i c
  fin_cases c
  · simp
  · exact h i

theorem polar_kernel_iff (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (v : V n) : (polarMatrix cs b).mulVec v = 0 ↔
      ∀ x : BitVec n, coefficientPolar cs b (decode v) x = false := by
  rw [polarMatrix_mulVec]
  constructor
  · intro hv
    have hf : polarFunctional cs b (decode v) = 0 := by
      apply functional_ext
      intro i
      exact congrFun hv i
    intro x
    have hh := LinearMap.congr_fun hf (coords x)
    change bitF (coefficientPolar cs b (decode v) (decode (coords x))) = 0 at hh
    rw [decode_coords] at hh
    exact bitF_injective hh
  · intro hv
    funext i
    change bitF (coefficientPolar cs b (decode v) (unitVec i)) = 0
    rw [hv]
    rfl

/-- Matrix surjectivity supplies alignment; no inverse or alignment is postulated. -/
theorem alignment_of_matrix_surjective
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (hs : Function.Surjective (polarMatrix cs b : Matrix (Fin n) (Fin n) F).mulVec) :
    ∀ u : BitVec n, ∃ a : BitVec n,
      ∀ x, coefficientPolar cs b a x = binaryDot u x := by
  intro u
  obtain ⟨v, hv⟩ := hs (fun i => dotFunctional u (Pi.single i 1))
  rw [polarMatrix_mulVec] at hv
  have heq : polarFunctional cs b (decode v) = dotFunctional u := by
    apply functional_ext
    intro i
    exact congrFun hv i
  refine ⟨decode v, ?_⟩
  intro x
  have hh := LinearMap.congr_fun heq (coords x)
  change bitF (coefficientPolar cs b (decode v) (decode (coords x))) =
    bitF (binaryDot u (decode (coords x))) at hh
  rw [decode_coords] at hh
  exact bitF_injective hh

/-- Exact semantic bridge from pointwise polar solvability to actual Walsh bentness. -/
theorem bent_of_polar_solvable
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (hs : ∀ u : BitVec n, ∃ a : BitVec n, ∀ x, coefficientPolar cs b a x = binaryDot u x) :
    IsBent (quadratic cs : BitVec n → BitVec m) b := by
  have hconst : ∀ u : BitVec n,
      walsh (quadratic cs) b u * walsh (quadratic cs) b u =
      walsh (quadratic cs) b (0 : BitVec n) * walsh (quadratic cs) b (0 : BitVec n) := by
    intro u
    obtain ⟨a, ha⟩ := hs u
    have hw := walsh_shift (quadratic cs) b u a (by
      intro x
      simp only [quadratic_component_correct]
      rw [quadraticComponent_translate, ha])
    rw [hw]
    cases binaryDot b (quadratic cs a) <;> simp [signed, Int.neg_mul_neg]
  have hp := QuadraticWalshParseval.walsh_parseval (quadratic cs : BitVec n → BitVec m) b
  simp only [hconst, QuadraticWalshParseval.sumDomain_const] at hp
  have hn : (↑(2^n : Nat) : Int) ≠ 0 := by
    have h : 0 < (2^n : Nat) := Nat.pow_pos (by decide)
    omega
  have hz := Int.eq_of_mul_eq_mul_left hn hp
  intro u
  exact (hconst u).trans hz

/-- Nonsingularity of the actual polar matrix gives actual Walsh bentness. -/
theorem bent_of_matrix_injective
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (hi : Function.Injective (polarMatrix cs b : Matrix (Fin n) (Fin n) F).mulVec) :
    IsBent (quadratic cs : BitVec n → BitVec m) b := by
  apply bent_of_polar_solvable cs b
  exact alignment_of_matrix_surjective cs b (Finite.surjective_of_injective hi)

/-- A supplied actual matrix-kernel vector decodes to a genuine Boolean radical witness. -/
theorem not_bent_of_matrix_kernel
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (v : V n)
    (hv : v ≠ 0) (hk : (polarMatrix cs b).mulVec v = 0) :
    ¬IsBent (quadratic cs : BitVec n → BitVec m) b := by
  apply QuadraticWalshRadical.quadratic_not_bent_of_radical cs b (decode v)
  · intro hz
    apply hv
    have h := congrArg coords hz
    simpa only [coords_decode, coords_zero] using h
  · intro e he
    exact (polar_kernel_iff cs b v).mp hk e

/-- Singularity of the actual polar matrix yields a nonzero radical, hence non-bentness. -/
theorem not_bent_of_matrix_not_injective
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (hi : ¬Function.Injective (polarMatrix cs b : Matrix (Fin n) (Fin n) F).mulVec) :
    ¬IsBent (quadratic cs : BitVec n → BitVec m) b := by
  classical
  simp only [Function.Injective, not_forall] at hi
  obtain ⟨v, w, h⟩ := hi
  have he : (polarMatrix cs b).mulVec v = (polarMatrix cs b).mulVec w := by tauto
  have hn : v ≠ w := by tauto
  apply not_bent_of_matrix_kernel cs b (v-w) (sub_ne_zero.mpr hn)
  rw [Matrix.mulVec_sub, he, sub_self]

theorem bent_iff_matrix_injective
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) :
    IsBent (quadratic cs : BitVec n → BitVec m) b ↔
      Function.Injective (polarMatrix cs b : Matrix (Fin n) (Fin n) F).mulVec := by
  classical
  constructor
  · intro hb
    by_contra hn
    exact not_bent_of_matrix_not_injective cs b hn hb
  · exact bent_of_matrix_injective cs b


/-- Definitionally the standard bilinear-form nondegeneracy condition.
Spelled out to avoid importing the much larger Properties module. -/
def Nondegenerate (B : V n →ₗ[F] V n →ₗ[F] F) : Prop :=
  ∀ v, (∀ w, B v w = 0) → v = 0

/-- The actual coefficient polar form, transported through the explicit codec. -/
def polarForm (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) :
    (V n →ₗ[F] V n →ₗ[F] F) where
  toFun v := polarFunctional cs b (decode v)
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change bitF (coefficientPolar cs b (decode (v+w)) (decode x)) = _
    rw [decode_add, coefficientPolar_add_left, bitF_xor]
    rfl
  map_smul' c v := by
    fin_cases c
    · apply LinearMap.ext
      intro x
      change bitF (coefficientPolar cs b (decode (0 • v)) (decode x)) = (0 : F) • _
      rw [zero_smul, decode_zero, coefficientPolar_zero_left, zero_smul]
      rfl
    · apply LinearMap.ext
      intro x
      change bitF (coefficientPolar cs b (decode (1 • v)) (decode x)) = (1 : F) • _
      simp only [one_smul]
      rfl

theorem polarForm_apply (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (v w : V n) : polarForm cs b v w = bitF (coefficientPolar cs b (decode v) (decode w)) := rfl

theorem nondegenerate_iff_matrix_injective
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) :
    Nondegenerate (polarForm cs b : (V n →ₗ[F] V n →ₗ[F] F)) ↔
      Function.Injective (polarMatrix cs b : Matrix (Fin n) (Fin n) F).mulVec := by
  constructor
  · intro hn v w hvw
    have hker : (polarMatrix cs b).mulVec (v-w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have hz := hn (v-w) (by
      intro x
      rw [polarForm_apply, (polar_kernel_iff cs b (v-w)).mp hker]
      rfl)
    exact sub_eq_zero.mp hz
  · intro hinj v hv
    apply hinj
    rw [Matrix.mulVec_zero, polarMatrix_mulVec]
    funext i
    exact hv (Pi.single i 1)

/-- Fully semantic generic bridge for the actual quadratic coefficient form. -/
theorem bent_iff_polarForm_nondegenerate
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) :
    IsBent (quadratic cs : BitVec n → BitVec m) b ↔
      Nondegenerate (polarForm cs b : (V n →ₗ[F] V n →ₗ[F] F)) := by
  rw [bent_iff_matrix_injective, nondegenerate_iff_matrix_injective]

/-- Integration interface: equality of actual polar forms, not an assumed rank criterion. -/
theorem bent_iff_nondegenerate_of_polarForm_eq
    (cs : List (Nat × Nat × BitVec m)) (b : BitVec m)
    (B : (V n →ₗ[F] V n →ₗ[F] F)) (hB : polarForm cs b = B) :
    IsBent (quadratic cs : BitVec n → BitVec m) b ↔ Nondegenerate B := by
  rw [← hB]
  exact bent_iff_polarForm_nondegenerate cs b

#print axioms bent_iff_polarForm_nondegenerate
#print axioms bent_iff_matrix_injective
#print axioms polarMatrix_entry
end QuadraticWalshMatrix
