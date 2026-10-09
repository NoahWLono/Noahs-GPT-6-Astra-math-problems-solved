import Data.C145
import Inputs.C001
import Inputs.C144
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C145
theorem input_certificate : signTree effective (BitVec.ofNat 8 145) = inputTree := by
  have hb : BitVec.ofNat 8 145 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 144) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C144.input_certificate]
  rfl
end N12.C145
