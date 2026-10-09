import Data.C214
import Inputs.C002
import Inputs.C212
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C214
theorem input_certificate : signTree effective (BitVec.ofNat 8 214) = inputTree := by
  have hb : BitVec.ofNat 8 214 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 212) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C212.input_certificate]
  rfl
end N12.C214
