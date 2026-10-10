import ProductCells

namespace ProgressivePool
open Finset Classical
variable {F I J Y : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Actual experiment endpoint for one fresh row event. The transcript-cell
factorization and finite-field conditioning estimate are both derived in this
proof chain. No independence of adaptive choices is postulated. -/
theorem actual_unspoiled_conditional_count
    (tree : QueryTree J (I → F) Y) (bs : List Bool)
    (feasible : ∃ bank, runBits rowTest bank tree = bs)
    (j : J) (w : I → F) (hw : w ≠ 0)
    (unspoiled : ∀ o ∈ pathObservations tree bs,
      o.row = j → o.input ≠ 0 → o.answer = false) :
    let cell := univ.filter fun bank : J → I → F => runBits rowTest bank tree = bs
    (Fintype.card F - (rowInputs (pathObservations tree bs) j).card) *
      (cell.filter fun bank => rowDot w (bank j) = 0).card ≤ cell.card := by
  obtain ⟨bank0,hbank0⟩ := feasible
  have ht := (actual_transcript_factorization rowTest bank0 tree bs).mp hbank0
  have hf : ∃ c, rowCompatible rowTest (pathObservations tree bs) j c :=
    ⟨bank0 j, ht.2 j⟩
  have hb := unspoiled_transcript_count (pathObservations tree bs) j hf unspoiled w hw
  dsimp only
  have he : (univ.filter fun bank : J → I → F => runBits rowTest bank tree = bs) =
      Fintype.piFinset (fun i => univ.filter
        (rowCompatible rowTest (pathObservations tree bs) i)) := by
    ext bank
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact (actual_transcript_factorization rowTest bank tree bs).trans (and_iff_right ht.1)
  rw [he]
  have hp := product_cell_local_bound
    (fun i => univ.filter (rowCompatible rowTest (pathObservations tree bs) i)) j
    (univ.filter fun c : I → F => rowDot w c = 0)
    (Fintype.card F - (rowInputs (pathObservations tree bs) j).card) hb
  simpa only [mem_filter, mem_univ, true_and] using hp

/-- A uniform denominator for all histories of length at most L, including
infeasible transcripts (whose cells are empty). -/
theorem actual_query_count_bound
    (tree : QueryTree J (I → F) Y) (bs : List Bool) (L : ℕ)
    (hlen : (pathObservations tree bs).length ≤ L)
    (j : J) (w : I → F) (hw : w ≠ 0)
    (unspoiled : ∀ o ∈ pathObservations tree bs,
      o.row = j → o.input ≠ 0 → o.answer = false) :
    let cell := univ.filter fun bank : J → I → F => runBits rowTest bank tree = bs
    (Fintype.card F - L) *
      (cell.filter fun bank => rowDot w (bank j) = 0).card ≤ cell.card := by
  by_cases hf : ∃ bank, runBits rowTest bank tree = bs
  · have hlocal := actual_unspoiled_conditional_count tree bs hf j w hw unspoiled
    have hi : (rowInputs (pathObservations tree bs) j).card ≤ L :=
      (rowInputs_card_le _ _).trans hlen
    exact (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hi _)).trans hlocal
  · have he : (univ.filter fun bank : J → I → F => runBits rowTest bank tree = bs) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro bank _ heq
      exact hf ⟨bank,heq⟩
    dsimp only
    rw [he]
    simp

#print axioms actual_query_count_bound
#print axioms actual_unspoiled_conditional_count
end ProgressivePool
