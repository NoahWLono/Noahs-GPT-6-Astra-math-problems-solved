import Data.C069
import Inputs.C001
import Inputs.C068
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C069
theorem input_certificate : signTree effective (BitVec.ofNat 8 69) = inputTree := by
  have hb : BitVec.ofNat 8 69 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 68) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C068.input_certificate]
  rfl
end N12.C069
