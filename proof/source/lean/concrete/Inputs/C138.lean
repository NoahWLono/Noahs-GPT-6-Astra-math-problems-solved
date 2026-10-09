import Data.C138
import Inputs.C002
import Inputs.C136
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C138
theorem input_certificate : signTree effective (BitVec.ofNat 8 138) = inputTree := by
  have hb : BitVec.ofNat 8 138 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 136) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C136.input_certificate]
  rfl
end N12.C138
