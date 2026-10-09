import Data.C200
import Inputs.C008
import Inputs.C192
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C200
theorem input_certificate : signTree effective (BitVec.ofNat 8 200) = inputTree := by
  have hb : BitVec.ofNat 8 200 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 192) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C192.input_certificate]
  rfl
end N12.C200
