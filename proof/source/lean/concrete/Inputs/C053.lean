import Data.C053
import Inputs.C001
import Inputs.C052
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C053
theorem input_certificate : signTree effective (BitVec.ofNat 8 53) = inputTree := by
  have hb : BitVec.ofNat 8 53 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 52) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C052.input_certificate]
  rfl
end N12.C053
