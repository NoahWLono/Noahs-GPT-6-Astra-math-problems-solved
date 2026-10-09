import Data.C098
import Inputs.C002
import Inputs.C096
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C098
theorem input_certificate : signTree effective (BitVec.ofNat 8 98) = inputTree := by
  have hb : BitVec.ofNat 8 98 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 96) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C096.input_certificate]
  rfl
end N12.C098
