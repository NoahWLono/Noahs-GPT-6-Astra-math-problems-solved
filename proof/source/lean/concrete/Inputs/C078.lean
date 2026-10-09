import Data.C078
import Inputs.C002
import Inputs.C076
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C078
theorem input_certificate : signTree effective (BitVec.ofNat 8 78) = inputTree := by
  have hb : BitVec.ofNat 8 78 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 76) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C076.input_certificate]
  rfl
end N12.C078
