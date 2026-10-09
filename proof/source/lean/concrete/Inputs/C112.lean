import Data.C112
import Inputs.C016
import Inputs.C096
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C112
theorem input_certificate : signTree effective (BitVec.ofNat 8 112) = inputTree := by
  have hb : BitVec.ofNat 8 112 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 96) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C096.input_certificate]
  rfl
end N12.C112
