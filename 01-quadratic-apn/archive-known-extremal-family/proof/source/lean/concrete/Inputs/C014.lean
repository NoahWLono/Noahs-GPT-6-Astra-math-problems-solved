import Data.C014
import Inputs.C002
import Inputs.C012
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C014
theorem input_certificate : signTree effective (BitVec.ofNat 8 14) = inputTree := by
  have hb : BitVec.ofNat 8 14 = (BitVec.ofNat 8 2 ^^^ BitVec.ofNat 8 12) := by decide
  rw [hb, signTree_xor, C002.input_certificate, C012.input_certificate]
  rfl
end N12.C014
