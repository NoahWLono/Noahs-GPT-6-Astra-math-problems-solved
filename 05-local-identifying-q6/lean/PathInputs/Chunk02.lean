import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk2 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk2 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c101 := ?_, c102 := ?_, c103 := ?_, c104 := ?_, c105 := ?_, c106 := ?_, c107 := ?_, c108 := ?_, c109 := ?_, c110 := ?_, c111 := ?_, c112 := ?_, c113 := ?_, c114 := ?_, c115 := ?_, c116 := ?_, c117 := ?_, c118 := ?_, c119 := ?_, c120 := ?_, c121 := ?_, c122 := ?_, c123 := ?_, c124 := ?_, c125 := ?_, c126 := ?_, c127 := ?_, c128 := ?_, c129 := ?_, c130 := ?_, c131 := ?_, c132 := ?_, c133 := ?_, c134 := ?_, c135 := ?_, c136 := ?_, c137 := ?_, c138 := ?_, c139 := ?_, c140 := ?_, c141 := ?_, c142 := ?_, c143 := ?_, c144 := ?_, c145 := ?_, c146 := ?_, c147 := ?_, c148 := ?_, c149 := ?_, c150 := ?_ }
  · have hh := (separationClause_sat (assignment X) C hA 8 9).mpr (hC.2 8 9 (by decide))
    rw [sep_data_36] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 8 10).mpr (hC.2 8 10 (by decide))
    rw [sep_data_37] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 8 12).mpr (hC.2 8 12 (by decide))
    rw [sep_data_38] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 8 24).mpr (hC.2 8 24 (by decide))
    rw [sep_data_39] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 8 40).mpr (hC.2 8 40 (by decide))
    rw [sep_data_40] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 9 11).mpr (hC.2 9 11 (by decide))
    rw [sep_data_41] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 9 13).mpr (hC.2 9 13 (by decide))
    rw [sep_data_42] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 9 25).mpr (hC.2 9 25 (by decide))
    rw [sep_data_43] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 9 41).mpr (hC.2 9 41 (by decide))
    rw [sep_data_44] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 10 11).mpr (hC.2 10 11 (by decide))
    rw [sep_data_45] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 10 14).mpr (hC.2 10 14 (by decide))
    rw [sep_data_46] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 10 26).mpr (hC.2 10 26 (by decide))
    rw [sep_data_47] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 10 42).mpr (hC.2 10 42 (by decide))
    rw [sep_data_48] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 11 15).mpr (hC.2 11 15 (by decide))
    rw [sep_data_49] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 11 27).mpr (hC.2 11 27 (by decide))
    rw [sep_data_50] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 11 43).mpr (hC.2 11 43 (by decide))
    rw [sep_data_51] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 12 13).mpr (hC.2 12 13 (by decide))
    rw [sep_data_52] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 12 14).mpr (hC.2 12 14 (by decide))
    rw [sep_data_53] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 12 28).mpr (hC.2 12 28 (by decide))
    rw [sep_data_54] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 12 44).mpr (hC.2 12 44 (by decide))
    rw [sep_data_55] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 13 15).mpr (hC.2 13 15 (by decide))
    rw [sep_data_56] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 13 29).mpr (hC.2 13 29 (by decide))
    rw [sep_data_57] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 13 45).mpr (hC.2 13 45 (by decide))
    rw [sep_data_58] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 14 15).mpr (hC.2 14 15 (by decide))
    rw [sep_data_59] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 14 30).mpr (hC.2 14 30 (by decide))
    rw [sep_data_60] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 14 46).mpr (hC.2 14 46 (by decide))
    rw [sep_data_61] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 15 31).mpr (hC.2 15 31 (by decide))
    rw [sep_data_62] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 15 47).mpr (hC.2 15 47 (by decide))
    rw [sep_data_63] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 16 17).mpr (hC.2 16 17 (by decide))
    rw [sep_data_64] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 16 18).mpr (hC.2 16 18 (by decide))
    rw [sep_data_65] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 16 20).mpr (hC.2 16 20 (by decide))
    rw [sep_data_66] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 16 24).mpr (hC.2 16 24 (by decide))
    rw [sep_data_67] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 16 48).mpr (hC.2 16 48 (by decide))
    rw [sep_data_68] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 17 19).mpr (hC.2 17 19 (by decide))
    rw [sep_data_69] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 17 21).mpr (hC.2 17 21 (by decide))
    rw [sep_data_70] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 17 25).mpr (hC.2 17 25 (by decide))
    rw [sep_data_71] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 17 49).mpr (hC.2 17 49 (by decide))
    rw [sep_data_72] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 18 19).mpr (hC.2 18 19 (by decide))
    rw [sep_data_73] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 18 22).mpr (hC.2 18 22 (by decide))
    rw [sep_data_74] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 18 26).mpr (hC.2 18 26 (by decide))
    rw [sep_data_75] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 18 50).mpr (hC.2 18 50 (by decide))
    rw [sep_data_76] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 19 23).mpr (hC.2 19 23 (by decide))
    rw [sep_data_77] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 19 27).mpr (hC.2 19 27 (by decide))
    rw [sep_data_78] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 19 51).mpr (hC.2 19 51 (by decide))
    rw [sep_data_79] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 20 21).mpr (hC.2 20 21 (by decide))
    rw [sep_data_80] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 20 22).mpr (hC.2 20 22 (by decide))
    rw [sep_data_81] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 20 28).mpr (hC.2 20 28 (by decide))
    rw [sep_data_82] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 20 52).mpr (hC.2 20 52 (by decide))
    rw [sep_data_83] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 21 23).mpr (hC.2 21 23 (by decide))
    rw [sep_data_84] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 21 29).mpr (hC.2 21 29 (by decide))
    rw [sep_data_85] at hh
    simpa [CNF.Clause.eval] using hh
end LocalIdentifyingQ6
