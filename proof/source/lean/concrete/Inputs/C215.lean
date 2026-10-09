import Data.C215
import Inputs.C001
import Inputs.C214
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C215
theorem input_certificate : signTree effective (BitVec.ofNat 8 215) = inputTree := by
  have hb : BitVec.ofNat 8 215 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 214) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C214.input_certificate]
  rfl
end N12.C215
