import Inputs.C054
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C054
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 54) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 54)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 432), (1, 360), (2, 504), (3, 2182), (4, 3269), (5, 1799), (6, 1046), (7, 1565), (8, 2087), (9, 160), (10, 240), (11, 280)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 54) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 54) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 54) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C054
