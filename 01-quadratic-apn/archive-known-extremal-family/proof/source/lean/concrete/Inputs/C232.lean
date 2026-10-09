import Data.C232
import Inputs.C008
import Inputs.C224
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C232
theorem input_certificate : signTree effective (BitVec.ofNat 8 232) = inputTree := by
  have hb : BitVec.ofNat 8 232 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 224) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C224.input_certificate]
  rfl
end N12.C232
