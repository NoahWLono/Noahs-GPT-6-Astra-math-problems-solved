import Data.C189
import Inputs.C001
import Inputs.C188
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C189
theorem input_certificate : signTree effective (BitVec.ofNat 8 189) = inputTree := by
  have hb : BitVec.ofNat 8 189 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 188) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C188.input_certificate]
  rfl
end N12.C189
