import Data.C208
import Inputs.C016
import Inputs.C192
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C208
theorem input_certificate : signTree effective (BitVec.ofNat 8 208) = inputTree := by
  have hb : BitVec.ofNat 8 208 = (BitVec.ofNat 8 16 ^^^ BitVec.ofNat 8 192) := by decide
  rw [hb, signTree_xor, C016.input_certificate, C192.input_certificate]
  rfl
end N12.C208
