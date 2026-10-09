import Data.C234
import Inputs.C002
import Inputs.C232
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C234
theorem input_certificate : signTree effective (BitVec.ofNat 8 234) = inputTree := by
  have hb : BitVec.ofNat 8 234 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 232) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C232.input_certificate]
  rfl
end N12.C234
