import Inputs.C206
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C206
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 206) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 206)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2328), (1, 3512), (2, 1776), (3, 3779), (4, 967), (5, 2950), (6, 1564), (7, 3646), (8, 3123), (9, 252), (10, 462), (11, 427)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 206) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 206) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 206) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C206
