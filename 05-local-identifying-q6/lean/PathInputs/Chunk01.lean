import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk1 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk1 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c51 := ?_, c52 := ?_, c53 := ?_, c54 := ?_, c55 := ?_, c56 := ?_, c57 := ?_, c58 := ?_, c59 := ?_, c60 := ?_, c61 := ?_, c62 := ?_, c63 := ?_, c64 := ?_, c65 := ?_, c66 := ?_, c67 := ?_, c68 := ?_, c69 := ?_, c70 := ?_, c71 := ?_, c72 := ?_, c73 := ?_, c74 := ?_, c75 := ?_, c76 := ?_, c77 := ?_, c78 := ?_, c79 := ?_, c80 := ?_, c81 := ?_, c82 := ?_, c83 := ?_, c84 := ?_, c85 := ?_, c86 := ?_, c87 := ?_, c88 := ?_, c89 := ?_, c90 := ?_, c91 := ?_, c92 := ?_, c93 := ?_, c94 := ?_, c95 := ?_, c96 := ?_, c97 := ?_, c98 := ?_, c99 := ?_, c100 := ?_ }
  · have hh := (dominationClause_sat (assignment X) C hA 50).mpr (hC.1 50)
    rw [dom_data_50] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 51).mpr (hC.1 51)
    rw [dom_data_51] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 52).mpr (hC.1 52)
    rw [dom_data_52] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 53).mpr (hC.1 53)
    rw [dom_data_53] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 54).mpr (hC.1 54)
    rw [dom_data_54] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 55).mpr (hC.1 55)
    rw [dom_data_55] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 56).mpr (hC.1 56)
    rw [dom_data_56] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 57).mpr (hC.1 57)
    rw [dom_data_57] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 58).mpr (hC.1 58)
    rw [dom_data_58] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 59).mpr (hC.1 59)
    rw [dom_data_59] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 60).mpr (hC.1 60)
    rw [dom_data_60] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 61).mpr (hC.1 61)
    rw [dom_data_61] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 62).mpr (hC.1 62)
    rw [dom_data_62] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (dominationClause_sat (assignment X) C hA 63).mpr (hC.1 63)
    rw [dom_data_63] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 0 1).mpr (hC.2 0 1 (by decide))
    rw [sep_data_0] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 0 2).mpr (hC.2 0 2 (by decide))
    rw [sep_data_1] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 0 4).mpr (hC.2 0 4 (by decide))
    rw [sep_data_2] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 0 8).mpr (hC.2 0 8 (by decide))
    rw [sep_data_3] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 0 16).mpr (hC.2 0 16 (by decide))
    rw [sep_data_4] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 0 32).mpr (hC.2 0 32 (by decide))
    rw [sep_data_5] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 1 3).mpr (hC.2 1 3 (by decide))
    rw [sep_data_6] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 1 5).mpr (hC.2 1 5 (by decide))
    rw [sep_data_7] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 1 9).mpr (hC.2 1 9 (by decide))
    rw [sep_data_8] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 1 17).mpr (hC.2 1 17 (by decide))
    rw [sep_data_9] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 1 33).mpr (hC.2 1 33 (by decide))
    rw [sep_data_10] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 2 3).mpr (hC.2 2 3 (by decide))
    rw [sep_data_11] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 2 6).mpr (hC.2 2 6 (by decide))
    rw [sep_data_12] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 2 10).mpr (hC.2 2 10 (by decide))
    rw [sep_data_13] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 2 18).mpr (hC.2 2 18 (by decide))
    rw [sep_data_14] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 2 34).mpr (hC.2 2 34 (by decide))
    rw [sep_data_15] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 3 7).mpr (hC.2 3 7 (by decide))
    rw [sep_data_16] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 3 11).mpr (hC.2 3 11 (by decide))
    rw [sep_data_17] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 3 19).mpr (hC.2 3 19 (by decide))
    rw [sep_data_18] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 3 35).mpr (hC.2 3 35 (by decide))
    rw [sep_data_19] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 4 5).mpr (hC.2 4 5 (by decide))
    rw [sep_data_20] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 4 6).mpr (hC.2 4 6 (by decide))
    rw [sep_data_21] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 4 12).mpr (hC.2 4 12 (by decide))
    rw [sep_data_22] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 4 20).mpr (hC.2 4 20 (by decide))
    rw [sep_data_23] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 4 36).mpr (hC.2 4 36 (by decide))
    rw [sep_data_24] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 5 7).mpr (hC.2 5 7 (by decide))
    rw [sep_data_25] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 5 13).mpr (hC.2 5 13 (by decide))
    rw [sep_data_26] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 5 21).mpr (hC.2 5 21 (by decide))
    rw [sep_data_27] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 5 37).mpr (hC.2 5 37 (by decide))
    rw [sep_data_28] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 6 7).mpr (hC.2 6 7 (by decide))
    rw [sep_data_29] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 6 14).mpr (hC.2 6 14 (by decide))
    rw [sep_data_30] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 6 22).mpr (hC.2 6 22 (by decide))
    rw [sep_data_31] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 6 38).mpr (hC.2 6 38 (by decide))
    rw [sep_data_32] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 7 15).mpr (hC.2 7 15 (by decide))
    rw [sep_data_33] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 7 23).mpr (hC.2 7 23 (by decide))
    rw [sep_data_34] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 7 39).mpr (hC.2 7 39 (by decide))
    rw [sep_data_35] at hh
    simpa [CNF.Clause.eval] using hh
end LocalIdentifyingQ6
