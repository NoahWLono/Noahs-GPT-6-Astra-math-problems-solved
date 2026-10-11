import RUPPath.Inputs
import GraphClauseData
import CardinalityEncoding
open Std.Sat
namespace LocalIdentifyingQ6
open CardinalityEncoding
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem semanticChunk4 (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.InputChunk4 (fun n => assignment X n = true) := by
  have hA : ∀ v : Vertex, assignment X (v.val+1) = C v := by
    intro v
    rw [assignment_input X _ (by have := v.isLt; omega)]
    exact hX v
  refine { c201 := ?_, c202 := ?_, c203 := ?_, c204 := ?_, c205 := ?_, c206 := ?_, c207 := ?_, c208 := ?_, c209 := ?_, c210 := ?_, c211 := ?_, c212 := ?_, c213 := ?_, c214 := ?_, c215 := ?_, c216 := ?_, c217 := ?_, c218 := ?_, c219 := ?_, c220 := ?_, c221 := ?_, c222 := ?_, c223 := ?_, c224 := ?_, c225 := ?_, c226 := ?_, c227 := ?_, c228 := ?_, c229 := ?_, c230 := ?_, c231 := ?_, c232 := ?_, c233 := ?_, c234 := ?_, c235 := ?_, c236 := ?_, c237 := ?_, c238 := ?_, c239 := ?_, c240 := ?_, c241 := ?_, c242 := ?_, c243 := ?_, c244 := ?_, c245 := ?_, c246 := ?_, c247 := ?_, c248 := ?_, c249 := ?_, c250 := ?_ }
  · have hh := (separationClause_sat (assignment X) C hA 38 46).mpr (hC.2 38 46 (by decide))
    rw [sep_data_136] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 38 54).mpr (hC.2 38 54 (by decide))
    rw [sep_data_137] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 39 47).mpr (hC.2 39 47 (by decide))
    rw [sep_data_138] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 39 55).mpr (hC.2 39 55 (by decide))
    rw [sep_data_139] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 40 41).mpr (hC.2 40 41 (by decide))
    rw [sep_data_140] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 40 42).mpr (hC.2 40 42 (by decide))
    rw [sep_data_141] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 40 44).mpr (hC.2 40 44 (by decide))
    rw [sep_data_142] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 40 56).mpr (hC.2 40 56 (by decide))
    rw [sep_data_143] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 41 43).mpr (hC.2 41 43 (by decide))
    rw [sep_data_144] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 41 45).mpr (hC.2 41 45 (by decide))
    rw [sep_data_145] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 41 57).mpr (hC.2 41 57 (by decide))
    rw [sep_data_146] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 42 43).mpr (hC.2 42 43 (by decide))
    rw [sep_data_147] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 42 46).mpr (hC.2 42 46 (by decide))
    rw [sep_data_148] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 42 58).mpr (hC.2 42 58 (by decide))
    rw [sep_data_149] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 43 47).mpr (hC.2 43 47 (by decide))
    rw [sep_data_150] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 43 59).mpr (hC.2 43 59 (by decide))
    rw [sep_data_151] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 44 45).mpr (hC.2 44 45 (by decide))
    rw [sep_data_152] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 44 46).mpr (hC.2 44 46 (by decide))
    rw [sep_data_153] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 44 60).mpr (hC.2 44 60 (by decide))
    rw [sep_data_154] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 45 47).mpr (hC.2 45 47 (by decide))
    rw [sep_data_155] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 45 61).mpr (hC.2 45 61 (by decide))
    rw [sep_data_156] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 46 47).mpr (hC.2 46 47 (by decide))
    rw [sep_data_157] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 46 62).mpr (hC.2 46 62 (by decide))
    rw [sep_data_158] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 47 63).mpr (hC.2 47 63 (by decide))
    rw [sep_data_159] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 48 49).mpr (hC.2 48 49 (by decide))
    rw [sep_data_160] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 48 50).mpr (hC.2 48 50 (by decide))
    rw [sep_data_161] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 48 52).mpr (hC.2 48 52 (by decide))
    rw [sep_data_162] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 48 56).mpr (hC.2 48 56 (by decide))
    rw [sep_data_163] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 49 51).mpr (hC.2 49 51 (by decide))
    rw [sep_data_164] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 49 53).mpr (hC.2 49 53 (by decide))
    rw [sep_data_165] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 49 57).mpr (hC.2 49 57 (by decide))
    rw [sep_data_166] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 50 51).mpr (hC.2 50 51 (by decide))
    rw [sep_data_167] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 50 54).mpr (hC.2 50 54 (by decide))
    rw [sep_data_168] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 50 58).mpr (hC.2 50 58 (by decide))
    rw [sep_data_169] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 51 55).mpr (hC.2 51 55 (by decide))
    rw [sep_data_170] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 51 59).mpr (hC.2 51 59 (by decide))
    rw [sep_data_171] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 52 53).mpr (hC.2 52 53 (by decide))
    rw [sep_data_172] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 52 54).mpr (hC.2 52 54 (by decide))
    rw [sep_data_173] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 52 60).mpr (hC.2 52 60 (by decide))
    rw [sep_data_174] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 53 55).mpr (hC.2 53 55 (by decide))
    rw [sep_data_175] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 53 61).mpr (hC.2 53 61 (by decide))
    rw [sep_data_176] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 54 55).mpr (hC.2 54 55 (by decide))
    rw [sep_data_177] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 54 62).mpr (hC.2 54 62 (by decide))
    rw [sep_data_178] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 55 63).mpr (hC.2 55 63 (by decide))
    rw [sep_data_179] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 56 57).mpr (hC.2 56 57 (by decide))
    rw [sep_data_180] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 56 58).mpr (hC.2 56 58 (by decide))
    rw [sep_data_181] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 56 60).mpr (hC.2 56 60 (by decide))
    rw [sep_data_182] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 57 59).mpr (hC.2 57 59 (by decide))
    rw [sep_data_183] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 57 61).mpr (hC.2 57 61 (by decide))
    rw [sep_data_184] at hh
    simpa [CNF.Clause.eval] using hh
  · have hh := (separationClause_sat (assignment X) C hA 58 59).mpr (hC.2 58 59 (by decide))
    rw [sep_data_185] at hh
    simpa [CNF.Clause.eval] using hh
end LocalIdentifyingQ6
