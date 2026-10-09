import Data.C127
import Inputs.C001
import Inputs.C126
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C127
theorem input_certificate : signTree effective (BitVec.ofNat 8 127) = inputTree := by
  have hb : BitVec.ofNat 8 127 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 126) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C126.input_certificate]
  rfl
end N12.C127
