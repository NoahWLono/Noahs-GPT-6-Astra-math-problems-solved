import Data.C243
import Inputs.C001
import Inputs.C242
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C243
theorem input_certificate : signTree effective (BitVec.ofNat 8 243) = inputTree := by
  have hb : BitVec.ofNat 8 243 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 242) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C242.input_certificate]
  rfl
end N12.C243
