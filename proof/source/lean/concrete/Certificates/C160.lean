import Inputs.C160
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C160
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 160) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 160)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 136), (1, 224), (2, 272), (3, 1153), (4, 1732), (5, 2306), (6, 530), (7, 2075), (8, 1060), (9, 80), (10, 280), (11, 160)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 160) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 160) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 160) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C160
