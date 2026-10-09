import Inputs.C216
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C216
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 216) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 216)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3776), (1, 960), (2, 2944), (3, 1536), (4, 3584), (5, 3072), (6, 515), (7, 2055), (8, 1030), (9, 95), (10, 313), (11, 181)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 216) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 216) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 216) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C216
