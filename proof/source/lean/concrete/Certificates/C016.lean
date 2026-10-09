import Inputs.C016
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C016
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 16) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 16)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 320), (1, 128), (2, 64), (3, 2560), (4, 1024), (5, 512), (6, 2565), (7, 1026), (8, 513), (9, 360), (10, 144), (11, 72)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 16) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 16) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 16) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C016
