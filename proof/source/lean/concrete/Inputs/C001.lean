import Data.C001
import Basis.B0_00
import Basis.B0_01
import Basis.B0_02
import Basis.B0_03
import Basis.B0_04
import Basis.B0_05
import Basis.B0_06
import Basis.B0_07
import Basis.B0_08
import Basis.B0_09
import Basis.B0_10
import Basis.B0_11
import Basis.B0_12
import Basis.B0_13
import Basis.B0_14
import Basis.B0_15
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C001
theorem input_certificate : signTree effective (BitVec.ofNat 8 1) = inputTree := by
  unfold signTree
  simp only [B0.scalar_correct]
  change (Tree.node (Tree.node (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 0 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 1 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 2 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 3 x)) 1)))) (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 4 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 5 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 6 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 7 x)) 1))))) (Tree.node (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 8 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 9 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 10 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 11 x)) 1)))) (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 12 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 13 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 14 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B0.scalar (embed 15 x)) 1)))))) = (Tree.node (Tree.node (Tree.node (Tree.node data8_0 data8_1) (Tree.node data8_2 data8_3)) (Tree.node (Tree.node data8_0 data8_4) (Tree.node data8_2 data8_5))) (Tree.node (Tree.node (Tree.node data8_6 data8_7) (Tree.node data8_8 data8_9)) (Tree.node (Tree.node data8_6 data8_10) (Tree.node data8_8 data8_11))))
  rw [inputBlock0, inputBlock1, inputBlock2, inputBlock3, inputBlock4, inputBlock5, inputBlock6, inputBlock7, inputBlock8, inputBlock9, inputBlock10, inputBlock11, inputBlock12, inputBlock13, inputBlock14, inputBlock15]
end N12.C001
