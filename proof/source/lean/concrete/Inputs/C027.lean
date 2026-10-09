import Data.C027
import Inputs.C001
import Inputs.C026
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C027
theorem input_certificate : signTree effective (BitVec.ofNat 8 27) = inputTree := by
  have hb : BitVec.ofNat 8 27 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 26) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C026.input_certificate]
  rfl
end N12.C027
