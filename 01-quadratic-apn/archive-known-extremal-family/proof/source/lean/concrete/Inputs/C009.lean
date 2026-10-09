import Data.C009
import Inputs.C001
import Inputs.C008
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C009
theorem input_certificate : signTree effective (BitVec.ofNat 8 9) = inputTree := by
  have hb : BitVec.ofNat 8 9 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 8) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C008.input_certificate]
  rfl
end N12.C009
