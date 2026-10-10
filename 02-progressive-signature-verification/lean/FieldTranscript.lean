import AdaptiveTranscript

namespace ProgressivePool
open Finset Classical
variable {F I J : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [DecidableEq J]

def rowTest (c w : I → F) : Bool := decide (rowDot w c = 0)

def rowInputs (obs : List (Observation J (I → F))) (j : J) : Finset (I → F) :=
  ((obs.filter fun o => o.row = j).map Observation.input).toFinset.erase 0

theorem mem_rowInputs (obs : List (Observation J (I → F))) (j : J) (v : I → F) :
    v ∈ rowInputs obs j ↔ v ≠ 0 ∧ ∃ o ∈ obs, o.row = j ∧ o.input = v := by
  simp [rowInputs, List.mem_map, List.mem_filter, and_assoc]

theorem rowInputs_card_le (obs : List (Observation J (I → F))) (j : J) :
    (rowInputs obs j).card ≤ obs.length := by
  calc
    (rowInputs obs j).card ≤
        ((obs.filter fun o => o.row = j).map Observation.input).toFinset.card :=
      card_erase_le
    _ ≤ ((obs.filter fun o => o.row = j).map Observation.input).length :=
      List.toFinset_card_le _
    _ = (obs.filter fun o => o.row = j).length := List.length_map _
    _ ≤ obs.length := List.length_filter_le _ _

theorem unspoiled_row_compatible (obs : List (Observation J (I → F))) (j : J)
    (feasible : ∃ c, rowCompatible rowTest obs j c)
    (unspoiled : ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false)
    (c : I → F) :
    rowCompatible rowTest obs j c ↔
      ∀ v ∈ rowInputs obs j, rowDot v c ≠ 0 := by
  constructor
  · intro hc v hv
    obtain ⟨hv0,o,ho,hj,hi⟩ := (mem_rowInputs obs j v).mp hv
    have ha := hc o ho hj
    have hz := unspoiled o ho hj (by simpa [hi] using hv0)
    simpa [rowTest, hz, hi] using ha
  · intro hc o ho hj
    by_cases hv : o.input = 0
    · obtain ⟨c0,hc0⟩ := feasible
      have ha := hc0 o ho hj
      have hz : rowTest c0 o.input = true := by simp [rowTest, hv, rowDot]
      have hz' : rowTest c o.input = true := by simp [rowTest, hv, rowDot]
      exact hz'.trans (hz.symm.trans ha)
    · have hm : o.input ∈ rowInputs obs j :=
        (mem_rowInputs obs j o.input).mpr ⟨hv,o,ho,hj,rfl⟩
      have hn := hc o.input hm
      rw [unspoiled o ho hj hv]
      simp [rowTest, hn]

theorem unspoiled_row_cell (obs : List (Observation J (I → F))) (j : J)
    (feasible : ∃ c, rowCompatible rowTest obs j c)
    (unspoiled : ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false) :
    (univ.filter (rowCompatible rowTest obs j)) =
      univ \ (rowInputs obs j).biUnion
        (fun v => univ.filter fun c : I → F => rowDot v c = 0) := by
  ext c
  simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_biUnion]
  rw [unspoiled_row_compatible obs j feasible unspoiled c]
  simp

/-- The finite-field conditional count bound on an actual feasible unspoiled
row transcript. The algebraic probability estimate is not a premise. -/
theorem unspoiled_transcript_count (obs : List (Observation J (I → F))) (j : J)
    (feasible : ∃ c, rowCompatible rowTest obs j c)
    (unspoiled : ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false)
    (w : I → F) (hw : w ≠ 0) :
    let cell := univ.filter (rowCompatible rowTest obs j)
    (Fintype.card F - (rowInputs obs j).card) *
      (cell ∩ (univ.filter fun c => rowDot w c = 0)).card ≤ cell.card := by
  dsimp
  rw [unspoiled_row_cell obs j feasible unspoiled]
  apply uniform_row_conditioned_count (rowInputs obs j) w _ hw
  intro v hv
  exact ((mem_rowInputs obs j v).mp hv).1

#print axioms unspoiled_transcript_count
end ProgressivePool
