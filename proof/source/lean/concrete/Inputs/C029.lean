import Data.C029
import Inputs.C001
import Inputs.C028
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C029
theorem input_certificate : signTree effective (BitVec.ofNat 8 29) = inputTree := by
  have hb : BitVec.ofNat 8 29 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 28) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C028.input_certificate]
  rfl
end N12.C029
