import Data.C099
import Inputs.C001
import Inputs.C098
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C099
theorem input_certificate : signTree effective (BitVec.ofNat 8 99) = inputTree := by
  have hb : BitVec.ofNat 8 99 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 98) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C098.input_certificate]
  rfl
end N12.C099
