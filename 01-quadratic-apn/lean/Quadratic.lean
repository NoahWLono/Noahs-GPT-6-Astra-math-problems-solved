import FastWalsh
namespace FastWalsh

theorem binaryDot_zero (b : BitVec n) : binaryDot b 0 = false := by
  induction n with
  | zero => simp [binaryDot]
  | succ n ih =>
    have h := binaryDot_cons b.msb false (b.setWidth n) (0 : BitVec n)
    have hz := ih (b.setWidth n)
    have h0 : BitVec.cons false (0 : BitVec n) = (0 : BitVec (n+1)) := BitVec.false_cons_zero
    simpa only [BitVec.cons_msb_setWidth, BitVec.false_cons_zero, Bool.and_false, Bool.xor_false, hz, h0] using h

theorem dot_xor_bool (a b c d e : Bool) :
    ((d ^^ e) ^^ (a && (b ^^ c))) = ((d ^^ (a && b)) ^^ (e ^^ (a && c))) := by
  decide +revert

theorem binaryDot_xor_right : ∀ (b x y : BitVec n),
    binaryDot b (x ^^^ y) = (binaryDot b x ^^ binaryDot b y) := by
  induction n with
  | zero => simp [binaryDot]
  | succ n ih =>
    rw [BitVec.forall_cons_iff]
    intro a b
    rw [BitVec.forall_cons_iff]
    intro c x
    rw [BitVec.forall_cons_iff]
    intro d y
    simp only [BitVec.cons_xor_cons, binaryDot_cons, ih]
    exact dot_xor_bool a c d _ _

def quadratic {n m : Nat} : List (Nat × Nat × BitVec m) → BitVec n → BitVec m
  | [], _ => 0
  | c::cs, x => (if x.getLsbD c.1 && x.getLsbD c.2.1 then c.2.2 else 0) ^^^ quadratic cs x

def quadraticComponent {n m : Nat} : List (Nat × Nat × BitVec m) → BitVec m → BitVec n → Bool
  | [], _, _ => false
  | c::cs, b, x => (binaryDot b c.2.2 && (x.getLsbD c.1 && x.getLsbD c.2.1)) ^^ quadraticComponent cs b x

theorem quadratic_component_correct (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) (x : BitVec n) :
    binaryDot b (quadratic cs x) = quadraticComponent cs b x := by
  induction cs with
  | nil => exact binaryDot_zero b
  | cons c cs ih =>
    cases h : (x.getLsbD c.1 && x.getLsbD c.2.1) <;>
      simp [quadratic, quadraticComponent, h, binaryDot_xor_right, binaryDot_zero, ih]

#print axioms quadratic_component_correct
end FastWalsh
