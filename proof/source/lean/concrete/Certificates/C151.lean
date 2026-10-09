import Inputs.C151
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C151
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 151) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 151)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 256), (1, 384), (2, 192), (3, 2240), (4, 3520), (5, 1920), (6, 3612), (7, 574), (8, 2611), (9, 480), (10, 112), (11, 344)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 151) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 151) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 151) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C151
