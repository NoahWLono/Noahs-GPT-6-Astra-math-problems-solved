import Data.C100
import Inputs.C004
import Inputs.C096
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C100
theorem input_certificate : signTree effective (BitVec.ofNat 8 100) = inputTree := by
  have hb : BitVec.ofNat 8 100 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 96) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C096.input_certificate]
  rfl
end N12.C100
