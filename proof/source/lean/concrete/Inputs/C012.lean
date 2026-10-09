import Data.C012
import Inputs.C004
import Inputs.C008
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C012
theorem input_certificate : signTree effective (BitVec.ofNat 8 12) = inputTree := by
  have hb : BitVec.ofNat 8 12 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 8) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C008.input_certificate]
  rfl
end N12.C012
