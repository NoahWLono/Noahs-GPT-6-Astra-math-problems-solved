import Data.C054
import Inputs.C002
import Inputs.C052
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C054
theorem input_certificate : signTree effective (BitVec.ofNat 8 54) = inputTree := by
  have hb : BitVec.ofNat 8 54 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 52) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C052.input_certificate]
  rfl
end N12.C054
