import Data.C025
import Inputs.C001
import Inputs.C024
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C025
theorem input_certificate : signTree effective (BitVec.ofNat 8 25) = inputTree := by
  have hb : BitVec.ofNat 8 25 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 24) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C024.input_certificate]
  rfl
end N12.C025
