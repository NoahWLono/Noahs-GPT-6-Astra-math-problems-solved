import Data.C238
import Inputs.C002
import Inputs.C236
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C238
theorem input_certificate : signTree effective (BitVec.ofNat 8 238) = inputTree := by
  have hb : BitVec.ofNat 8 238 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 236) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C236.input_certificate]
  rfl
end N12.C238
