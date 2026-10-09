import Data.C168
import Inputs.C008
import Inputs.C160
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C168
theorem input_certificate : signTree effective (BitVec.ofNat 8 168) = inputTree := by
  have hb : BitVec.ofNat 8 168 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 160) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C160.input_certificate]
  rfl
end N12.C168
