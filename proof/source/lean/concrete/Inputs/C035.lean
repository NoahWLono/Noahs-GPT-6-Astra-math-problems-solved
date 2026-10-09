import Data.C035
import Inputs.C001
import Inputs.C034
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C035
theorem input_certificate : signTree effective (BitVec.ofNat 8 35) = inputTree := by
  have hb : BitVec.ofNat 8 35 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 34) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C034.input_certificate]
  rfl
end N12.C035
