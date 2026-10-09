import Basis.B5
import Data.C032
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C032
theorem inputBlock1 : tabulate (fun x => signed (B5.scalar (embed 1 x)) 1) = data8_0 := by rfl
end N12.C032
