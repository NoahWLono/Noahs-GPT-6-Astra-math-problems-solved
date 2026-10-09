import Data.C070
import Inputs.C002
import Inputs.C068
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C070
theorem input_certificate : signTree effective (BitVec.ofNat 8 70) = inputTree := by
  have hb : BitVec.ofNat 8 70 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 68) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C068.input_certificate]
  rfl
end N12.C070
