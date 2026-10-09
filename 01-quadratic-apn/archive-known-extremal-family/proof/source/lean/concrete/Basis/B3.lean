import Definitions
open FastWalsh
namespace N12.B3
def scalar (x : BitVec 12) : Bool := ((x.getLsbD 3 && x.getLsbD 6) ^^ ((x.getLsbD 4 && x.getLsbD 8) ^^ (x.getLsbD 5 && x.getLsbD 7)))
theorem dotCoeff0 : binaryDot (BitVec.ofNat 8 8) (0 : BitVec 8) = false := by decide
theorem dotCoeff1 : binaryDot (BitVec.ofNat 8 8) (1 : BitVec 8) = false := by decide
theorem dotCoeff2 : binaryDot (BitVec.ofNat 8 8) (2 : BitVec 8) = false := by decide
theorem dotCoeff3 : binaryDot (BitVec.ofNat 8 8) (3 : BitVec 8) = false := by decide
theorem dotCoeff4 : binaryDot (BitVec.ofNat 8 8) (4 : BitVec 8) = false := by decide
theorem dotCoeff8 : binaryDot (BitVec.ofNat 8 8) (8 : BitVec 8) = true := by decide
theorem dotCoeff16 : binaryDot (BitVec.ofNat 8 8) (16 : BitVec 8) = false := by decide
theorem dotCoeff32 : binaryDot (BitVec.ofNat 8 8) (32 : BitVec 8) = false := by decide
theorem dotCoeff48 : binaryDot (BitVec.ofNat 8 8) (48 : BitVec 8) = false := by decide
theorem dotCoeff64 : binaryDot (BitVec.ofNat 8 8) (64 : BitVec 8) = false := by decide
theorem dotCoeff72 : binaryDot (BitVec.ofNat 8 8) (72 : BitVec 8) = true := by decide
theorem dotCoeff128 : binaryDot (BitVec.ofNat 8 8) (128 : BitVec 8) = false := by decide
theorem dotCoeff129 : binaryDot (BitVec.ofNat 8 8) (129 : BitVec 8) = false := by decide
theorem dotCoeff130 : binaryDot (BitVec.ofNat 8 8) (130 : BitVec 8) = false := by decide
theorem dotCoeff144 : binaryDot (BitVec.ofNat 8 8) (144 : BitVec 8) = false := by decide
theorem dotCoeff192 : binaryDot (BitVec.ofNat 8 8) (192 : BitVec 8) = false := by decide
theorem dotCoeff196 : binaryDot (BitVec.ofNat 8 8) (196 : BitVec 8) = false := by decide
theorem scalar_correct (x : BitVec 12) : binaryDot (BitVec.ofNat 8 8) (effective x) = scalar x := by
  rw [effective, quadratic_component_correct]
  simp only [coefficients, quadraticComponent, dotCoeff0, dotCoeff1, dotCoeff2, dotCoeff3, dotCoeff4, dotCoeff8, dotCoeff16, dotCoeff32, dotCoeff48, dotCoeff64, dotCoeff72, dotCoeff128, dotCoeff129, dotCoeff130, dotCoeff144, dotCoeff192, dotCoeff196, Bool.false_and, Bool.true_and, Bool.false_xor, Bool.xor_false, scalar]
end N12.B3
