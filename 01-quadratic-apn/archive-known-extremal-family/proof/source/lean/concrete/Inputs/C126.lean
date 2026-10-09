import Data.C126
import Inputs.C002
import Inputs.C124
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C126
theorem input_certificate : signTree effective (BitVec.ofNat 8 126) = inputTree := by
  have hb : BitVec.ofNat 8 126 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 124) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C124.input_certificate]
  rfl
end N12.C126
