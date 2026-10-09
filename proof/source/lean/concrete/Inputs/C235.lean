import Data.C235
import Inputs.C001
import Inputs.C234
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C235
theorem input_certificate : signTree effective (BitVec.ofNat 8 235) = inputTree := by
  have hb : BitVec.ofNat 8 235 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 234) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C234.input_certificate]
  rfl
end N12.C235
