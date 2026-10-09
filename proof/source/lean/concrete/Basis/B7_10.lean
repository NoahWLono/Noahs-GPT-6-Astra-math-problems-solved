import Basis.B7
import Data.C128
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C128
theorem inputBlock10 : tabulate (fun x => signed (B7.scalar (embed 10 x)) 1) = data8_10 := by rfl
end N12.C128
