import Data.C216
import Inputs.C008
import Inputs.C208
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C216
theorem input_certificate : signTree effective (BitVec.ofNat 8 216) = inputTree := by
  have hb : BitVec.ofNat 8 216 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 208) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C208.input_certificate]
  rfl
end N12.C216
