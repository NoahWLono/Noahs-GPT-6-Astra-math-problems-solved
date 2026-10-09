import Data.C132
import Inputs.C004
import Inputs.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C132
theorem input_certificate : signTree effective (BitVec.ofNat 8 132) = inputTree := by
  have hb : BitVec.ofNat 8 132 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 128) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C128.input_certificate]
  rfl
end N12.C132
