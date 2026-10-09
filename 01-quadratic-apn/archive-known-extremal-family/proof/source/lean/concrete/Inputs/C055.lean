import Data.C055
import Inputs.C001
import Inputs.C054
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C055
theorem input_certificate : signTree effective (BitVec.ofNat 8 55) = inputTree := by
  have hb : BitVec.ofNat 8 55 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 54) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C054.input_certificate]
  rfl
end N12.C055
