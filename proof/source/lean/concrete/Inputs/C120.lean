import Data.C120
import Inputs.C008
import Inputs.C112
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C120
theorem input_certificate : signTree effective (BitVec.ofNat 8 120) = inputTree := by
  have hb : BitVec.ofNat 8 120 = (BitVec.ofNat 8 8 ^^^ BitVec.ofNat 8 112) := by decide
  rw [hb, signTree_xor, C008.input_certificate, C112.input_certificate]
  rfl
end N12.C120
