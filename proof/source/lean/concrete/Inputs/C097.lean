import Data.C097
import Inputs.C001
import Inputs.C096
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C097
theorem input_certificate : signTree effective (BitVec.ofNat 8 97) = inputTree := by
  have hb : BitVec.ofNat 8 97 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 96) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C096.input_certificate]
  rfl
end N12.C097
