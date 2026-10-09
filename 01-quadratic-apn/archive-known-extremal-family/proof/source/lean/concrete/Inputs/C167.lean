import Data.C167
import Inputs.C001
import Inputs.C166
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C167
theorem input_certificate : signTree effective (BitVec.ofNat 8 167) = inputTree := by
  have hb : BitVec.ofNat 8 167 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 166) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C166.input_certificate]
  rfl
end N12.C167
