import Data.C041
import Inputs.C001
import Inputs.C040
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C041
theorem input_certificate : signTree effective (BitVec.ofNat 8 41) = inputTree := by
  have hb : BitVec.ofNat 8 41 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 40) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C040.input_certificate]
  rfl
end N12.C041
