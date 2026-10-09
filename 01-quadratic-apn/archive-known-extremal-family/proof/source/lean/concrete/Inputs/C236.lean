import Data.C236
import Inputs.C004
import Inputs.C232
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C236
theorem input_certificate : signTree effective (BitVec.ofNat 8 236) = inputTree := by
  have hb : BitVec.ofNat 8 236 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 232) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C232.input_certificate]
  rfl
end N12.C236
