import Data.C179
import Inputs.C001
import Inputs.C178
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C179
theorem input_certificate : signTree effective (BitVec.ofNat 8 179) = inputTree := by
  have hb : BitVec.ofNat 8 179 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 178) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C178.input_certificate]
  rfl
end N12.C179
