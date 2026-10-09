import Data.C252
import Inputs.C004
import Inputs.C248
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C252
theorem input_certificate : signTree effective (BitVec.ofNat 8 252) = inputTree := by
  have hb : BitVec.ofNat 8 252 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 248) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C248.input_certificate]
  rfl
end N12.C252
