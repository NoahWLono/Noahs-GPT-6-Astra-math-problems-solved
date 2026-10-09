import Data.C005
import Inputs.C001
import Inputs.C004
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C005
theorem input_certificate : signTree effective (BitVec.ofNat 8 5) = inputTree := by
  have hb : BitVec.ofNat 8 5 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 4) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C004.input_certificate]
  rfl
end N12.C005
