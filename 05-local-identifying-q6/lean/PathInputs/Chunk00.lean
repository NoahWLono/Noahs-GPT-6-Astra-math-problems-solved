import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk0 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk0 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c1 := ?_, c2 := ?_, c3 := ?_, c4 := ?_, c5 := ?_, c6 := ?_, c7 := ?_, c8 := ?_, c9 := ?_, c10 := ?_, c11 := ?_, c12 := ?_, c13 := ?_, c14 := ?_, c15 := ?_, c16 := ?_, c17 := ?_, c18 := ?_, c19 := ?_, c20 := ?_, c21 := ?_, c22 := ?_, c23 := ?_, c24 := ?_, c25 := ?_, c26 := ?_, c27 := ?_, c28 := ?_, c29 := ?_, c30 := ?_, c31 := ?_, c32 := ?_, c33 := ?_, c34 := ?_, c35 := ?_, c36 := ?_, c37 := ?_, c38 := ?_, c39 := ?_, c40 := ?_, c41 := ?_, c42 := ?_, c43 := ?_, c44 := ?_, c45 := ?_, c46 := ?_, c47 := ?_, c48 := ?_, c49 := ?_, c50 := ?_ }
  · have hh := (dominationClause_sat (assignment X) C hA 0).mpr (hC.1 0)
    rw [dom_data_0] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 1).mpr (hC.1 1)
    rw [dom_data_1] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 2).mpr (hC.1 2)
    rw [dom_data_2] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 3).mpr (hC.1 3)
    rw [dom_data_3] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 4).mpr (hC.1 4)
    rw [dom_data_4] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 5).mpr (hC.1 5)
    rw [dom_data_5] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 6).mpr (hC.1 6)
    rw [dom_data_6] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 7).mpr (hC.1 7)
    rw [dom_data_7] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 8).mpr (hC.1 8)
    rw [dom_data_8] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 9).mpr (hC.1 9)
    rw [dom_data_9] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 10).mpr (hC.1 10)
    rw [dom_data_10] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 11).mpr (hC.1 11)
    rw [dom_data_11] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 12).mpr (hC.1 12)
    rw [dom_data_12] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 13).mpr (hC.1 13)
    rw [dom_data_13] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 14).mpr (hC.1 14)
    rw [dom_data_14] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 15).mpr (hC.1 15)
    rw [dom_data_15] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 16).mpr (hC.1 16)
    rw [dom_data_16] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 17).mpr (hC.1 17)
    rw [dom_data_17] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 18).mpr (hC.1 18)
    rw [dom_data_18] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 19).mpr (hC.1 19)
    rw [dom_data_19] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 20).mpr (hC.1 20)
    rw [dom_data_20] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 21).mpr (hC.1 21)
    rw [dom_data_21] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 22).mpr (hC.1 22)
    rw [dom_data_22] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 23).mpr (hC.1 23)
    rw [dom_data_23] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 24).mpr (hC.1 24)
    rw [dom_data_24] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 25).mpr (hC.1 25)
    rw [dom_data_25] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 26).mpr (hC.1 26)
    rw [dom_data_26] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 27).mpr (hC.1 27)
    rw [dom_data_27] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 28).mpr (hC.1 28)
    rw [dom_data_28] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 29).mpr (hC.1 29)
    rw [dom_data_29] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 30).mpr (hC.1 30)
    rw [dom_data_30] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 31).mpr (hC.1 31)
    rw [dom_data_31] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 32).mpr (hC.1 32)
    rw [dom_data_32] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 33).mpr (hC.1 33)
    rw [dom_data_33] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 34).mpr (hC.1 34)
    rw [dom_data_34] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 35).mpr (hC.1 35)
    rw [dom_data_35] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 36).mpr (hC.1 36)
    rw [dom_data_36] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 37).mpr (hC.1 37)
    rw [dom_data_37] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 38).mpr (hC.1 38)
    rw [dom_data_38] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 39).mpr (hC.1 39)
    rw [dom_data_39] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 40).mpr (hC.1 40)
    rw [dom_data_40] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 41).mpr (hC.1 41)
    rw [dom_data_41] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 42).mpr (hC.1 42)
    rw [dom_data_42] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 43).mpr (hC.1 43)
    rw [dom_data_43] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 44).mpr (hC.1 44)
    rw [dom_data_44] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 45).mpr (hC.1 45)
    rw [dom_data_45] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 46).mpr (hC.1 46)
    rw [dom_data_46] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 47).mpr (hC.1 47)
    rw [dom_data_47] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 48).mpr (hC.1 48)
    rw [dom_data_48] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 49).mpr (hC.1 49)
    rw [dom_data_49] at hh
    simpa [CNF.Clause.eval] using hh
end LocalIdentifyingQ6
