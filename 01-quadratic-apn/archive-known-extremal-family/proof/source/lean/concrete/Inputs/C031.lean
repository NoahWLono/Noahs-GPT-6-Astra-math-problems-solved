import Data.C031
import Inputs.C001
import Inputs.C030
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C031
theorem input_certificate : signTree effective (BitVec.ofNat 8 31) = inputTree := by
  have hb : BitVec.ofNat 8 31 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 30) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C030.input_certificate]
  rfl
end N12.C031
