import Data.C240
import Inputs.C016
import Inputs.C224
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C240
theorem input_certificate : signTree effective (BitVec.ofNat 8 240) = inputTree := by
  have hb : BitVec.ofNat 8 240 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 224) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C224.input_certificate]
  rfl
end N12.C240
