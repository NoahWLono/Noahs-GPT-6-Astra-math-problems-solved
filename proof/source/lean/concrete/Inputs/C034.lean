import Data.C034
import Inputs.C002
import Inputs.C032
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C034
theorem input_certificate : signTree effective (BitVec.ofNat 8 34) = inputTree := by
  have hb : BitVec.ofNat 8 34 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 32) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C032.input_certificate]
  rfl
end N12.C034
