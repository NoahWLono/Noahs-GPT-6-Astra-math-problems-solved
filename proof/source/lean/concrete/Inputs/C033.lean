import Data.C033
import Inputs.C001
import Inputs.C032
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C033
theorem input_certificate : signTree effective (BitVec.ofNat 8 33) = inputTree := by
  have hb : BitVec.ofNat 8 33 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 32) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C032.input_certificate]
  rfl
end N12.C033
