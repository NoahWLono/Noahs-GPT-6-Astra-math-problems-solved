import Data.C023
import Inputs.C001
import Inputs.C022
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C023
theorem input_certificate : signTree effective (BitVec.ofNat 8 23) = inputTree := by
  have hb : BitVec.ofNat 8 23 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 22) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C022.input_certificate]
  rfl
end N12.C023
