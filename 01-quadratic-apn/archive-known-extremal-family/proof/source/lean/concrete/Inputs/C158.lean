import Data.C158
import Inputs.C002
import Inputs.C156
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C158
theorem input_certificate : signTree effective (BitVec.ofNat 8 158) = inputTree := by
  have hb : BitVec.ofNat 8 158 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 156) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C156.input_certificate]
  rfl
end N12.C158
