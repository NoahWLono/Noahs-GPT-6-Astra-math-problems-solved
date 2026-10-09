import Data.C222
import Inputs.C002
import Inputs.C220
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C222
theorem input_certificate : signTree effective (BitVec.ofNat 8 222) = inputTree := by
  have hb : BitVec.ofNat 8 222 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 220) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C220.input_certificate]
  rfl
end N12.C222
