import Basis.B2
import Data.C004
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C004
theorem inputBlock9 : tabulate (fun x => signed (B2.scalar (embed 9 x)) 1) = data8_4 := by rfl
end N12.C004
