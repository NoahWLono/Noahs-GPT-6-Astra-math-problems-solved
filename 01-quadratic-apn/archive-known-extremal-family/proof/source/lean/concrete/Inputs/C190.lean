import Data.C190
import Inputs.C002
import Inputs.C188
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C190
theorem input_certificate : signTree effective (BitVec.ofNat 8 190) = inputTree := by
  have hb : BitVec.ofNat 8 190 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 188) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C188.input_certificate]
  rfl
end N12.C190
