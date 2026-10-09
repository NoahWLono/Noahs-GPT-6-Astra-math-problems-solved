import Data.C068
import Inputs.C004
import Inputs.C064
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C068
theorem input_certificate : signTree effective (BitVec.ofNat 8 68) = inputTree := by
  have hb : BitVec.ofNat 8 68 = (BitVec.ofNat 8 4 ^^^ BitVec.ofNat 8 64) := by decide
  rw [hb, signTree_xor, C004.input_certificate, C064.input_certificate]
  rfl
end N12.C068
