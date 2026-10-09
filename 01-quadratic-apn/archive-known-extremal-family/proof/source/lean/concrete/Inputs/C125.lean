import Data.C125
import Inputs.C001
import Inputs.C124
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C125
theorem input_certificate : signTree effective (BitVec.ofNat 8 125) = inputTree := by
  have hb : BitVec.ofNat 8 125 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 124) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C124.input_certificate]
  rfl
end N12.C125
