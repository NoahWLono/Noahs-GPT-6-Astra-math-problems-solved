import Data.C030
import Inputs.C002
import Inputs.C028
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C030
theorem input_certificate : signTree effective (BitVec.ofNat 8 30) = inputTree := by
  have hb : BitVec.ofNat 8 30 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 28) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C028.input_certificate]
  rfl
end N12.C030
