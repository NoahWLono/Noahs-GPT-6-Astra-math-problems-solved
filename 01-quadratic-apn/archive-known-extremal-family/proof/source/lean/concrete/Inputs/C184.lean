import Data.C184
import Inputs.C008
import Inputs.C176
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C184
theorem input_certificate : signTree effective (BitVec.ofNat 8 184) = inputTree := by
  have hb : BitVec.ofNat 8 184 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 176) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C176.input_certificate]
  rfl
end N12.C184
