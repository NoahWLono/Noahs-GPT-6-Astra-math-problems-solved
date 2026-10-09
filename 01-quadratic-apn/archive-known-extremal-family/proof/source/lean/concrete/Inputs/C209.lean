import Data.C209
import Inputs.C001
import Inputs.C208
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C209
theorem input_certificate : signTree effective (BitVec.ofNat 8 209) = inputTree := by
  have hb : BitVec.ofNat 8 209 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 208) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C208.input_certificate]
  rfl
end N12.C209
