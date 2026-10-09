import Data.C203
import Inputs.C001
import Inputs.C202
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C203
theorem input_certificate : signTree effective (BitVec.ofNat 8 203) = inputTree := by
  have hb : BitVec.ofNat 8 203 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 202) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C202.input_certificate]
  rfl
end N12.C203
