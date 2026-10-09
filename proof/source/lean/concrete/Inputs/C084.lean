import Data.C084
import Inputs.C004
import Inputs.C080
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C084
theorem input_certificate : signTree effective (BitVec.ofNat 8 84) = inputTree := by
  have hb : BitVec.ofNat 8 84 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 80) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C080.input_certificate]
  rfl
end N12.C084
