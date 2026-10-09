import Data.C246
import Inputs.C002
import Inputs.C244
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C246
theorem input_certificate : signTree effective (BitVec.ofNat 8 246) = inputTree := by
  have hb : BitVec.ofNat 8 246 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 244) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C244.input_certificate]
  rfl
end N12.C246
