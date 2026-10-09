import Data.C124
import Inputs.C004
import Inputs.C120
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C124
theorem input_certificate : signTree effective (BitVec.ofNat 8 124) = inputTree := by
  have hb : BitVec.ofNat 8 124 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 120) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C120.input_certificate]
  rfl
end N12.C124
