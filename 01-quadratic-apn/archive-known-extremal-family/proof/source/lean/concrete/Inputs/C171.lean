import Data.C171
import Inputs.C001
import Inputs.C170
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C171
theorem input_certificate : signTree effective (BitVec.ofNat 8 171) = inputTree := by
  have hb : BitVec.ofNat 8 171 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 170) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C170.input_certificate]
  rfl
end N12.C171
