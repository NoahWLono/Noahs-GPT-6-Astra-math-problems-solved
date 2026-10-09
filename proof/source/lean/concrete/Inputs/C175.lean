import Data.C175
import Inputs.C001
import Inputs.C174
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C175
theorem input_certificate : signTree effective (BitVec.ofNat 8 175) = inputTree := by
  have hb : BitVec.ofNat 8 175 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 174) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C174.input_certificate]
  rfl
end N12.C175
