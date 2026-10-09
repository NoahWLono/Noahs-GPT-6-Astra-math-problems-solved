import Inputs.C035
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C035
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 35) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 35)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 160), (1, 240), (2, 280), (3, 1028), (4, 1542), (5, 2051), (6, 2050), (7, 3075), (8, 1540), (9, 272), (10, 408), (11, 224)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 35) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 35) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 35) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C035
