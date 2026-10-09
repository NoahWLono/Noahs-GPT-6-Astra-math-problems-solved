import Data.C075
import Inputs.C001
import Inputs.C074
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C075
theorem input_certificate : signTree effective (BitVec.ofNat 8 75) = inputTree := by
  have hb : BitVec.ofNat 8 75 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 74) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C074.input_certificate]
  rfl
end N12.C075
