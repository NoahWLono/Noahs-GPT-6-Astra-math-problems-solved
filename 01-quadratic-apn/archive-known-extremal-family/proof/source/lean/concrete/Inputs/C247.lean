import Data.C247
import Inputs.C001
import Inputs.C246
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C247
theorem input_certificate : signTree effective (BitVec.ofNat 8 247) = inputTree := by
  have hb : BitVec.ofNat 8 247 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 246) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C246.input_certificate]
  rfl
end N12.C247
