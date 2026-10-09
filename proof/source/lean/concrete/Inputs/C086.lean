import Data.C086
import Inputs.C002
import Inputs.C084
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C086
theorem input_certificate : signTree effective (BitVec.ofNat 8 86) = inputTree := by
  have hb : BitVec.ofNat 8 86 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 84) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C084.input_certificate]
  rfl
end N12.C086
