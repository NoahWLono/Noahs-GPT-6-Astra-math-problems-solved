import Data.C156
import Inputs.C004
import Inputs.C152
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C156
theorem input_certificate : signTree effective (BitVec.ofNat 8 156) = inputTree := by
  have hb : BitVec.ofNat 8 156 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 152) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C152.input_certificate]
  rfl
end N12.C156
