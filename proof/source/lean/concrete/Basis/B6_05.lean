import Basis.B6
import Data.C064
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C064
theorem inputBlock5 : tabulate (fun x => signed (B6.scalar (embed 5 x)) 1) = data8_5 := by rfl
end N12.C064
