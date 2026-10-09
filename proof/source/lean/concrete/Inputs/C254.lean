import Data.C254
import Inputs.C002
import Inputs.C252
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C254
theorem input_certificate : signTree effective (BitVec.ofNat 8 254) = inputTree := by
  have hb : BitVec.ofNat 8 254 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 252) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C252.input_certificate]
  rfl
end N12.C254
