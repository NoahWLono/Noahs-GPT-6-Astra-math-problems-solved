import Inputs.C024
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C024
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 24) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 24)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3904), (1, 640), (2, 2624), (3, 2560), (4, 1024), (5, 512), (6, 2565), (7, 1026), (8, 513), (9, 367), (10, 145), (11, 77)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 24) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 24) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 24) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C024
