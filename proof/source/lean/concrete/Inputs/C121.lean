import Data.C121
import Inputs.C001
import Inputs.C120
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C121
theorem input_certificate : signTree effective (BitVec.ofNat 8 121) = inputTree := by
  have hb : BitVec.ofNat 8 121 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 120) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C120.input_certificate]
  rfl
end N12.C121
