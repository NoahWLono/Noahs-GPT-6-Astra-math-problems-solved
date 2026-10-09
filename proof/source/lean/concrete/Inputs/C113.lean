import Data.C113
import Inputs.C001
import Inputs.C112
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C113
theorem input_certificate : signTree effective (BitVec.ofNat 8 113) = inputTree := by
  have hb : BitVec.ofNat 8 113 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 112) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C112.input_certificate]
  rfl
end N12.C113
