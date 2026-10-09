import Data.C169
import Inputs.C001
import Inputs.C168
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C169
theorem input_certificate : signTree effective (BitVec.ofNat 8 169) = inputTree := by
  have hb : BitVec.ofNat 8 169 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 168) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C168.input_certificate]
  rfl
end N12.C169
