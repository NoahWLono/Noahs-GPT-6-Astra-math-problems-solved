import Data.C219
import Inputs.C001
import Inputs.C218
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C219
theorem input_certificate : signTree effective (BitVec.ofNat 8 219) = inputTree := by
  have hb : BitVec.ofNat 8 219 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 218) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C218.input_certificate]
  rfl
end N12.C219
