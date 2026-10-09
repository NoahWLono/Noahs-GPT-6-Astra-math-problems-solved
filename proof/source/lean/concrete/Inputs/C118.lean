import Data.C118
import Inputs.C002
import Inputs.C116
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C118
theorem input_certificate : signTree effective (BitVec.ofNat 8 118) = inputTree := by
  have hb : BitVec.ofNat 8 118 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 116) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C116.input_certificate]
  rfl
end N12.C118
