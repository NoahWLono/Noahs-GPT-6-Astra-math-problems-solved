import Data.C013
import Inputs.C001
import Inputs.C012
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C013
theorem input_certificate : signTree effective (BitVec.ofNat 8 13) = inputTree := by
  have hb : BitVec.ofNat 8 13 = (BitVec.ofNat 8 1 ^^^ BitVec.ofNat 8 12) := by decide
  rw [hb, signTree_xor, C001.input_certificate, C012.input_certificate]
  rfl
end N12.C013
