import Data.C162
import Inputs.C002
import Inputs.C160
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C162
theorem input_certificate : signTree effective (BitVec.ofNat 8 162) = inputTree := by
  have hb : BitVec.ofNat 8 162 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 160) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C160.input_certificate]
  rfl
end N12.C162
