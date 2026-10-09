import FastWalsh
namespace FastWalsh
/-- Adding a zero output coordinate does not change the corresponding component. -/
def zeroExtend {n m : Nat} (f : BitVec n → BitVec m) : BitVec n → BitVec (m+1) :=
  fun x => BitVec.cons false (f x)

theorem binaryDot_zeroExtend (b : BitVec (m+1)) (x : BitVec m) :
    binaryDot b (BitVec.cons false x) = binaryDot (b.setWidth m) x := by
  simpa only [BitVec.cons_msb_setWidth, Bool.and_false, Bool.xor_false] using
    binaryDot_cons b.msb false (b.setWidth m) x

theorem fastBent_zeroExtend {n m : Nat} (f : BitVec n → BitVec m) (b : BitVec (m+1)) :
    fastBent (zeroExtend f) b = fastBent f (b.setWidth m) := by
  simp only [fastBent, fastWalsh, zeroExtend, binaryDot_zeroExtend]


#print axioms fastBent_zeroExtend
end FastWalsh
