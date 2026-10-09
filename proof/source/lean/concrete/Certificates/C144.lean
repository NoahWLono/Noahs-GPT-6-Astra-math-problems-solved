import Inputs.C144
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C144
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 144) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 144)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 192), (1, 448), (2, 384), (3, 1664), (4, 3776), (5, 3328), (6, 531), (7, 2079), (8, 1062), (9, 88), (10, 312), (11, 176)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 144) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 144) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 144) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C144
