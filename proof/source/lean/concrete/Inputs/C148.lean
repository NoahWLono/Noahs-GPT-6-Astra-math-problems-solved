import Data.C148
import Inputs.C004
import Inputs.C144
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C148
theorem input_certificate : signTree effective (BitVec.ofNat 8 148) = inputTree := by
  have hb : BitVec.ofNat 8 148 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 144) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C144.input_certificate]
  rfl
end N12.C148
