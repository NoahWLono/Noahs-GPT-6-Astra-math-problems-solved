import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk3 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk3 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c151 := ?_, c152 := ?_, c153 := ?_, c154 := ?_, c155 := ?_, c156 := ?_, c157 := ?_, c158 := ?_, c159 := ?_, c160 := ?_, c161 := ?_, c162 := ?_, c163 := ?_, c164 := ?_, c165 := ?_, c166 := ?_, c167 := ?_, c168 := ?_, c169 := ?_, c170 := ?_, c171 := ?_, c172 := ?_, c173 := ?_, c174 := ?_, c175 := ?_, c176 := ?_, c177 := ?_, c178 := ?_, c179 := ?_, c180 := ?_, c181 := ?_, c182 := ?_, c183 := ?_, c184 := ?_, c185 := ?_, c186 := ?_, c187 := ?_, c188 := ?_, c189 := ?_, c190 := ?_, c191 := ?_, c192 := ?_, c193 := ?_, c194 := ?_, c195 := ?_, c196 := ?_, c197 := ?_, c198 := ?_, c199 := ?_, c200 := ?_ }
  · have hh := (separationClause_sat (assignment X) C hA 21 53).mpr (hC.2 21 53 (by decide))
    rw [sep_data_86] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 22 23).mpr (hC.2 22 23 (by decide))
    rw [sep_data_87] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 22 30).mpr (hC.2 22 30 (by decide))
    rw [sep_data_88] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 22 54).mpr (hC.2 22 54 (by decide))
    rw [sep_data_89] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 23 31).mpr (hC.2 23 31 (by decide))
    rw [sep_data_90] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 23 55).mpr (hC.2 23 55 (by decide))
    rw [sep_data_91] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 24 25).mpr (hC.2 24 25 (by decide))
    rw [sep_data_92] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 24 26).mpr (hC.2 24 26 (by decide))
    rw [sep_data_93] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 24 28).mpr (hC.2 24 28 (by decide))
    rw [sep_data_94] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 24 56).mpr (hC.2 24 56 (by decide))
    rw [sep_data_95] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 25 27).mpr (hC.2 25 27 (by decide))
    rw [sep_data_96] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 25 29).mpr (hC.2 25 29 (by decide))
    rw [sep_data_97] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 25 57).mpr (hC.2 25 57 (by decide))
    rw [sep_data_98] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 26 27).mpr (hC.2 26 27 (by decide))
    rw [sep_data_99] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 26 30).mpr (hC.2 26 30 (by decide))
    rw [sep_data_100] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 26 58).mpr (hC.2 26 58 (by decide))
    rw [sep_data_101] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 27 31).mpr (hC.2 27 31 (by decide))
    rw [sep_data_102] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 27 59).mpr (hC.2 27 59 (by decide))
    rw [sep_data_103] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 28 29).mpr (hC.2 28 29 (by decide))
    rw [sep_data_104] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 28 30).mpr (hC.2 28 30 (by decide))
    rw [sep_data_105] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 28 60).mpr (hC.2 28 60 (by decide))
    rw [sep_data_106] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 29 31).mpr (hC.2 29 31 (by decide))
    rw [sep_data_107] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 29 61).mpr (hC.2 29 61 (by decide))
    rw [sep_data_108] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 30 31).mpr (hC.2 30 31 (by decide))
    rw [sep_data_109] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 30 62).mpr (hC.2 30 62 (by decide))
    rw [sep_data_110] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 31 63).mpr (hC.2 31 63 (by decide))
    rw [sep_data_111] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 32 33).mpr (hC.2 32 33 (by decide))
    rw [sep_data_112] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 32 34).mpr (hC.2 32 34 (by decide))
    rw [sep_data_113] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 32 36).mpr (hC.2 32 36 (by decide))
    rw [sep_data_114] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 32 40).mpr (hC.2 32 40 (by decide))
    rw [sep_data_115] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 32 48).mpr (hC.2 32 48 (by decide))
    rw [sep_data_116] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 33 35).mpr (hC.2 33 35 (by decide))
    rw [sep_data_117] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 33 37).mpr (hC.2 33 37 (by decide))
    rw [sep_data_118] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 33 41).mpr (hC.2 33 41 (by decide))
    rw [sep_data_119] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 33 49).mpr (hC.2 33 49 (by decide))
    rw [sep_data_120] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 34 35).mpr (hC.2 34 35 (by decide))
    rw [sep_data_121] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 34 38).mpr (hC.2 34 38 (by decide))
    rw [sep_data_122] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 34 42).mpr (hC.2 34 42 (by decide))
    rw [sep_data_123] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 34 50).mpr (hC.2 34 50 (by decide))
    rw [sep_data_124] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 35 39).mpr (hC.2 35 39 (by decide))
    rw [sep_data_125] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 35 43).mpr (hC.2 35 43 (by decide))
    rw [sep_data_126] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 35 51).mpr (hC.2 35 51 (by decide))
    rw [sep_data_127] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 36 37).mpr (hC.2 36 37 (by decide))
    rw [sep_data_128] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 36 38).mpr (hC.2 36 38 (by decide))
    rw [sep_data_129] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 36 44).mpr (hC.2 36 44 (by decide))
    rw [sep_data_130] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 36 52).mpr (hC.2 36 52 (by decide))
    rw [sep_data_131] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 37 39).mpr (hC.2 37 39 (by decide))
    rw [sep_data_132] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 37 45).mpr (hC.2 37 45 (by decide))
    rw [sep_data_133] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 37 53).mpr (hC.2 37 53 (by decide))
    rw [sep_data_134] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 38 39).mpr (hC.2 38 39 (by decide))
    rw [sep_data_135] at hh
    simpa [CNF.Clause.eval] using hh
end LocalIdentifyingQ6
