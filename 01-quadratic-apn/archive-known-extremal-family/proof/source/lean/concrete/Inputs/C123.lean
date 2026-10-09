import Data.C123
import Inputs.C001
import Inputs.C122
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C123
theorem input_certificate : signTree effective (BitVec.ofNat 8 123) = inputTree := by
  have hb : BitVec.ofNat 8 123 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 122) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C122.input_certificate]
  rfl
end N12.C123
