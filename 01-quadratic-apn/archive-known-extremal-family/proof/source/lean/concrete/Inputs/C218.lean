import Data.C218
import Inputs.C002
import Inputs.C216
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C218
theorem input_certificate : signTree effective (BitVec.ofNat 8 218) = inputTree := by
  have hb : BitVec.ofNat 8 218 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 216) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C216.input_certificate]
  rfl
end N12.C218
