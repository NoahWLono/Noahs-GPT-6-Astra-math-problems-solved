import Data.C087
import Inputs.C001
import Inputs.C086
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C087
theorem input_certificate : signTree effective (BitVec.ofNat 8 87) = inputTree := by
  have hb : BitVec.ofNat 8 87 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 86) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C086.input_certificate]
  rfl
end N12.C087
