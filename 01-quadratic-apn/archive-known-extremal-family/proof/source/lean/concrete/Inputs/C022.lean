import Data.C022
import Inputs.C002
import Inputs.C020
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C022
theorem input_certificate : signTree effective (BitVec.ofNat 8 22) = inputTree := by
  have hb : BitVec.ofNat 8 22 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 20) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C020.input_certificate]
  rfl
end N12.C022
