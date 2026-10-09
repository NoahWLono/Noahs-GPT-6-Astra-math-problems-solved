import Data.C176
import Inputs.C016
import Inputs.C160
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C176
theorem input_certificate : signTree effective (BitVec.ofNat 8 176) = inputTree := by
  have hb : BitVec.ofNat 8 176 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 160) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C160.input_certificate]
  rfl
end N12.C176
