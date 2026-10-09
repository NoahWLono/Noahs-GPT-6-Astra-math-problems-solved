import Data.C049
import Inputs.C001
import Inputs.C048
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C049
theorem input_certificate : signTree effective (BitVec.ofNat 8 49) = inputTree := by
  have hb : BitVec.ofNat 8 49 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 48) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C048.input_certificate]
  rfl
end N12.C049
