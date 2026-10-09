import Data.C157
import Inputs.C001
import Inputs.C156
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C157
theorem input_certificate : signTree effective (BitVec.ofNat 8 157) = inputTree := by
  have hb : BitVec.ofNat 8 157 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 156) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C156.input_certificate]
  rfl
end N12.C157
