import Data.C135
import Inputs.C001
import Inputs.C134
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C135
theorem input_certificate : signTree effective (BitVec.ofNat 8 135) = inputTree := by
  have hb : BitVec.ofNat 8 135 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 134) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C134.input_certificate]
  rfl
end N12.C135
