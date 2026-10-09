import Data.C048
import Inputs.C016
import Inputs.C032
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C048
theorem input_certificate : signTree effective (BitVec.ofNat 8 48) = inputTree := by
  have hb : BitVec.ofNat 8 48 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 32) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C032.input_certificate]
  rfl
end N12.C048
