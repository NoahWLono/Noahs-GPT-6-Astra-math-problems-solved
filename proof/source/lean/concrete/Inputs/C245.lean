import Data.C245
import Inputs.C001
import Inputs.C244
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C245
theorem input_certificate : signTree effective (BitVec.ofNat 8 245) = inputTree := by
  have hb : BitVec.ofNat 8 245 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 244) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C244.input_certificate]
  rfl
end N12.C245
