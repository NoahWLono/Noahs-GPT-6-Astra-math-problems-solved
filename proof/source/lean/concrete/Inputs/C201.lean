import Data.C201
import Inputs.C001
import Inputs.C200
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C201
theorem input_certificate : signTree effective (BitVec.ofNat 8 201) = inputTree := by
  have hb : BitVec.ofNat 8 201 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 200) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C200.input_certificate]
  rfl
end N12.C201
