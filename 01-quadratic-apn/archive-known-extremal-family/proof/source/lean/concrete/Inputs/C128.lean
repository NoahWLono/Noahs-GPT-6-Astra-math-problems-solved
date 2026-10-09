import Data.C128
import Basis.B7_00
import Basis.B7_01
import Basis.B7_02
import Basis.B7_03
import Basis.B7_04
import Basis.B7_05
import Basis.B7_06
import Basis.B7_07
import Basis.B7_08
import Basis.B7_09
import Basis.B7_10
import Basis.B7_11
import Basis.B7_12
import Basis.B7_13
import Basis.B7_14
import Basis.B7_15
open FastWalsh
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C128
theorem input_certificate : signTree effective (BitVec.ofNat 8 128) = inputTree := by
  unfold signTree
  simp only [B7.scalar_correct]
  change (Tree.node (Tree.node (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 0 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 1 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 2 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 3 x)) 1)))) (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 4 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 5 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 6 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 7 x)) 1))))) (Tree.node (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 8 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 9 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 10 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 11 x)) 1)))) (Tree.node (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 12 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 13 x)) 1))) (Tree.node (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 14 x)) 1)) (tabulate (fun x : BitVec 8 => signed (B7.scalar (embed 15 x)) 1)))))) = (Tree.node (Tree.node (Tree.node (Tree.node data8_0 data8_1) (Tree.node data8_2 data8_3)) (Tree.node (Tree.node data8_4 data8_5) (Tree.node data8_6 data8_7))) (Tree.node (Tree.node (Tree.node data8_8 data8_9) (Tree.node data8_10 data8_11)) (Tree.node (Tree.node data8_12 data8_13) (Tree.node data8_14 data8_15))))
  rw [inputBlock0, inputBlock1, inputBlock2, inputBlock3, inputBlock4, inputBlock5, inputBlock6, inputBlock7, inputBlock8, inputBlock9, inputBlock10, inputBlock11, inputBlock12, inputBlock13, inputBlock14, inputBlock15]
end N12.C128
