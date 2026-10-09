import Data.C154
import Inputs.C002
import Inputs.C152
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C154
theorem input_certificate : signTree effective (BitVec.ofNat 8 154) = inputTree := by
  have hb : BitVec.ofNat 8 154 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 152) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C152.input_certificate]
  rfl
end N12.C154
