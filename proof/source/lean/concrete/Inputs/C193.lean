import Data.C193
import Inputs.C001
import Inputs.C192
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C193
theorem input_certificate : signTree effective (BitVec.ofNat 8 193) = inputTree := by
  have hb : BitVec.ofNat 8 193 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 192) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C192.input_certificate]
  rfl
end N12.C193
