import FamilyAlgebra.PencilInjection
import Mathlib.Tactic.Ring

namespace FamilyAlgebra
variable {E : Type*} [Field E]

def complement (x : Pfaffian.Coordinates E) : Pfaffian.Coordinates E := fun i =>
  match i.val with
  | 0 => x 5 | 1 => x 4 | 2 => x 3 | 3 => x 2 | 4 => x 1 | _ => x 0

/-- Explicit Pfaffian-adjugate identity in characteristic two. -/
theorem complement_action (two_zero : (2:E)=0) (x : Pfaffian.Coordinates E)
    (y : TraceCoordinates.V4 E) (i : Fin 4) :
    TraceCoordinates.action (altMatrix (complement x))
      (TraceCoordinates.action (altMatrix x) y) i = Pfaffian.pf x * y i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 =>
    simp only [TraceCoordinates.action, TraceCoordinates.dot, altMatrix, complement, Pfaffian.pf]
    ring_nf
    simp only [two_zero, mul_zero, zero_mul, add_zero, zero_add]
    ac_rfl
  | i+4 => omega

/-- Nonzero Pfaffian gives a trivial matrix kernel without a determinant/rank
classification or an assumed inverse. -/
theorem pf_nonzero_kernel (two_zero : (2:E)=0) (x : Pfaffian.Coordinates E)
    (nonzero : Pfaffian.pf x ≠ 0) (y : TraceCoordinates.V4 E)
    (kernel : ∀ i, TraceCoordinates.action (altMatrix x) y i=0) : y=0 := by
  funext i
  have h := complement_action two_zero x y i
  have hz : TraceCoordinates.action (altMatrix (complement x))
      (TraceCoordinates.action (altMatrix x) y) i = 0 := by
    have hfun : TraceCoordinates.action (altMatrix x) y = fun _ => 0 := funext kernel
    rw [hfun]
    simp [TraceCoordinates.action, TraceCoordinates.dot]
  rw [hz] at h
  exact (mul_eq_zero.mp h.symm).resolve_left nonzero

/-- Inverse action, with the scalar division explicit. -/
theorem pf_inverse_action (two_zero : (2:E)=0) (x : Pfaffian.Coordinates E)
    (nonzero : Pfaffian.pf x ≠ 0) (y : TraceCoordinates.V4 E) (i : Fin 4) :
    (Pfaffian.pf x)⁻¹ * TraceCoordinates.action (altMatrix (complement x))
      (TraceCoordinates.action (altMatrix x) y) i = y i := by
  rw [complement_action two_zero, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

def baseWitness (u v w : Bool) : TraceCoordinates.V4 E := fun i => match i.val with
  | 0 => bit (u || v || !w)
  | 1 => bit (u || (!v && w))
  | 2 => bit (u ^^ v)
  | _ => 0

theorem baseWitness_nonzero (u v w : Bool) : (baseWitness u v w : TraceCoordinates.V4 E) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  cases u <;> cases v <;> cases w <;> simp [baseWitness, bit] at h0 h1

/-- Explicit nonzero kernel witnesses for all six singular base cases. -/
theorem baseWitness_kernel (two_zero : (2:E)=0) (u v w z : Bool)
    (singular : q (base u v w z)=false) (i : Fin 4) :
    TraceCoordinates.action (altMatrix (liftSix (base u v w z)))
      (baseWitness u v w : TraceCoordinates.V4 E) i=0 := by
  have h11 : (1:E)+1=0 := by simpa only [one_add_one_eq_two] using two_zero
  rcases i with ⟨i,hi⟩
  match i with
  | 0 | 1 | 2 | 3 =>
    cases u <;> cases v <;> cases w <;> cases z <;>
      simp_all [q, base, TraceCoordinates.action, TraceCoordinates.dot, altMatrix,
        liftSix, baseWitness, bit]
  | i+4 => omega

theorem zeroSix_coord (i : Fin 6) : sixCoord ⟨false,false,false,false,false,false⟩ i=false := by
  rcases i with ⟨i,hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | i+6 => omega

/-- Vanishing extension inputs reduce the actual pencil to its binary base. -/
theorem pencil_zero_extension (a : E) (n : Nat) (positive : 0<n)
    (u v w z : Bool) (s t : Nat → Bool)
    (inactive : ∀ j, 0<j → j<n → s j=false ∧ t j=false) :
    pencil a (family u v w z s t) n = liftSix (base u v w z) := by
  funext i
  rw [pencil_coord]
  have hc : ∀ j, j<n → sixCoord (family u v w z s t j) i = singletonBit 0 (sixCoord (base u v w z) i) j := by
    intro j hj
    by_cases hz : j=0
    · simp [hz, family, singletonBit]
    · rcases inactive j (by omega) hj with ⟨hs,ht⟩
      have hzero : family u v w z s t j = ⟨false,false,false,false,false,false⟩ := by
        simp [family, hz, hs, ht, oddPlane, evenPlane]
      rw [hzero, zeroSix_coord]
      simp [singletonBit, hz]
  rw [binarySum_congr _ _ _ n hc, binarySum_single _ 0 n _ positive, liftSix_coord]
  cases sixCoord (base u v w z) i <;> simp [bit]

/-- Every singular concrete pencil has an explicit nonzero kernel witness. -/
theorem singular_pencil_kernel (two_zero : (2:E)=0) (a : E)
    (n : Nat) (positive : 0<n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (u v w z : Bool) (s t : Nat → Bool)
    (singular : Pfaffian.pf (pencil a (family u v w z s t) n)=0) :
    ∃ y : TraceCoordinates.V4 E, y ≠ 0 ∧
      ∀ i, TraceCoordinates.action (altMatrix (pencil a (family u v w z s t) n)) y i=0 := by
  rcases (concrete_zero_locus two_zero a n positive independent u v w z s t).mp singular with ⟨hbase,hrest⟩
  refine ⟨baseWitness u v w, baseWitness_nonzero u v w, ?_⟩
  rw [pencil_zero_extension a n positive u v w z s t hrest]
  exact baseWitness_kernel two_zero u v w z hbase

#print axioms singular_pencil_kernel
#print axioms pf_nonzero_kernel
end FamilyAlgebra
