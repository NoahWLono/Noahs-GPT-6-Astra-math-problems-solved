import FinalResidual
import FreshSampling

namespace ProgressivePool
set_option maxHeartbeats 800000
open Finset Classical
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

noncomputable def finalZeroRows {s : ℕ}
    (tree : QueryTree (Fin s) (I → F) (I → F)) (bank : Fin s → I → F) :
    Finset (Fin s) := univ.filter fun j => rowDot (runOutput bank tree) (bank j) = 0

/-- End-to-end uniform-row bad-fraction theorem for arbitrary adaptive index/bit
queries and a final nonzero residual. All adaptive conditional counting is proved,
not assumed. This endpoint deliberately uses the conservative q-L-s denominator. -/
theorem uniform_pool_bad_count {s : ℕ}
    (tree : QueryTree (Fin s) (I → F) (I → F)) (L u : ℕ)
    (hdepth : queryHeight tree ≤ L)
    (hnonzero : ∀ bank, runOutput bank tree ≠ 0) :
    (Fintype.card F-(L+s))^u *
      (univ.filter fun bank : Fin s → I → F => u ≤ (finalZeroRows tree bank).card).card ≤
        (L+s).choose u * Fintype.card (Fin s → I → F) := by
  let ext := finalExperiment (univ : Finset (Fin s)).toList tree
  have hh : queryHeight ext ≤ L+s := by
    simpa [ext, finalExperiment_height] using Nat.add_le_add_right hdepth s
  have hl := markedExperiment_local [] ext (L+s) (by simpa using hh)
  have he : historyCell ([] : List (Observation (Fin s) (I → F))) = univ := by
    ext bank
    simp [historyCell, historyCompatible]
  rw [he] at hl
  have hb := AdaptiveTail.marked_event_bound (Fintype.card F-(L+s)) (L+s) u univ
    (univ.filter fun bank : Fin s → I → F => u ≤ (finalZeroRows tree bank).card)
    (markedExperiment [] ext) (markedExperiment_depth [] ext (L+s) hh) hl
    (filter_subset _ _) (by
      intro bank hbank
      exact (mem_filter.mp hbank).2 |>.trans (final_zero_le_spoils bank tree (hnonzero bank)))
  simpa using hb

theorem uniform_pool_bad_fraction {s : ℕ}
    (tree : QueryTree (Fin s) (I → F) (I → F)) (L u : ℕ)
    (hdepth : queryHeight tree ≤ L)
    (hnonzero : ∀ bank, runOutput bank tree ≠ 0)
    (hfield : L+s < Fintype.card F) :
    ((univ.filter fun bank : Fin s → I → F => u ≤ (finalZeroRows tree bank).card).card : ℚ) /
      (Fintype.card (Fin s → I → F) : ℚ) ≤
        ((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u := by
  have ht : (0 : ℚ) < Fintype.card (Fin s → I → F) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hd : (0 : ℚ) < ((Fintype.card F-(L+s) : ℕ) : ℚ)^u :=
    pow_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hfield)) _
  apply (div_le_div_iff₀ ht hd).mpr
  have hb := uniform_pool_bad_count tree L u hdepth hnonzero
  exact_mod_cast (by simpa [Nat.mul_comm] using hb)

/-- The explicit one-epoch experiment: uniform secret bank, adaptive prior
queries, fixed final residual and threshold, then genuinely fresh index strings.
The threshold may be any function of the prior state, never of the fresh draws. -/
theorem uniform_pool_progressive {s : ℕ} (hs : 0 < s)
    (tree : QueryTree (Fin s) (I → F) (I → F)) (L u : ℕ)
    (hdepth : queryHeight tree ≤ L)
    (hnonzero : ∀ bank, runOutput bank tree ≠ 0)
    (hfield : L+s < Fintype.card F) (T : (Fin s → I → F) → ℕ) :
    FreshSampling.acceptMass univ
      (fun _ : Fin s → I → F => 1 / (Fintype.card (Fin s → I → F) : ℚ))
      (finalZeroRows tree) T ≤
    (∑ bank : Fin s → I → F, (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T bank)) /
      (Fintype.card (Fin s → I → F) : ℚ) +
        ((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u := by
  have hm := FreshSampling.fresh_threshold_uniform (u := u) hs univ
    (finalZeroRows tree) T (fun bank => u ≤ (finalZeroRows tree bank).card)
    (by intro bank _ h; omega)
  have hb := uniform_pool_bad_fraction tree L u hdepth hnonzero hfield
  simp only [card_univ] at hm
  apply le_trans hm
  apply add_le_add
  · exact le_rfl
  · convert hb using 1 <;> congr 2
    congr 1
    ext bank
    simp

#print axioms uniform_pool_bad_count
#print axioms uniform_pool_bad_fraction
#print axioms uniform_pool_progressive
end ProgressivePool
