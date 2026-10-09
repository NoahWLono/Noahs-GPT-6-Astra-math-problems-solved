import Data.C237
import Inputs.C001
import Inputs.C236
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C237
theorem input_certificate : signTree effective (BitVec.ofNat 8 237) = inputTree := by
  have hb : BitVec.ofNat 8 237 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 236) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C236.input_certificate]
  rfl
end N12.C237
