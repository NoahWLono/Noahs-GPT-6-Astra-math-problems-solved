import Inputs.C208
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C208
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 208) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 208)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1216), (1, 1984), (2, 2432), (3, 1536), (4, 3584), (5, 3072), (6, 515), (7, 2055), (8, 1030), (9, 90), (10, 315), (11, 180)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 208) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 208) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 208) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C208
