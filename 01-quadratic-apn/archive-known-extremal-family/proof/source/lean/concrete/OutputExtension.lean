import Extension
import ZeroSum
namespace FastWalsh

theorem walsh_zeroExtend {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec (m+1)) (u : BitVec n) :
    walsh (zeroExtend f) b u = walsh f (b.setWidth m) u := by
  simp only [walsh, zeroExtend, binaryDot_zeroExtend]

theorem isBent_zeroExtend {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec (m+1)) :
    IsBent (zeroExtend f) b ↔ IsBent f (b.setWidth m) := by
  simp only [IsBent, walsh_zeroExtend]

def liftCoefficients (cs : List (Nat × Nat × BitVec m)) : List (Nat × Nat × BitVec (m+1)) :=
  cs.map fun c => (c.1, c.2.1, BitVec.cons false c.2.2)

theorem quadratic_zeroExtend (cs : List (Nat × Nat × BitVec m)) :
    zeroExtend (quadratic cs : BitVec n → BitVec m) = quadratic (liftCoefficients cs) := by
  funext x
  induction cs with
  | nil => exact BitVec.false_cons_zero
  | cons c cs ih =>
    simp only [zeroExtend, liftCoefficients] at ih
    have h0 : BitVec.cons false (0 : BitVec m) = (0 : BitVec (m+1)) := BitVec.false_cons_zero
    cases h : (x.getLsbD c.1 && x.getLsbD c.2.1) <;>
      simp [zeroExtend, quadratic, liftCoefficients, h, ← ih, BitVec.cons_xor_cons, h0]

#print axioms quadratic_zeroExtend
#print axioms isBent_zeroExtend
end FastWalsh
