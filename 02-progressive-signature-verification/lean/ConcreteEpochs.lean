import UniformPoolEndpoint
import EpochComposition

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

/-- Incoming public history selects a complete bounded adaptive query strategy.
Only the current bank is accessible through those queries. The transition may
retain arbitrary information for later epochs; the next bank is independent. -/
structure PoolEpoch (s : ℕ) (H : Type*) (F I : Type*) where
  query : H → QueryTree (Fin s) (I → F) (I → F)
  next : H → (Fin s → I → F) → H
  invoke : H → (Fin s → I → F) → Bool

noncomputable def PoolEpoch.toEpoch {s : ℕ} (e : PoolEpoch s H F I) (u : ℕ) :
    EpochComposition.Epoch H (Fin s → I → F) where
  next := e.next
  bad h bank := e.invoke h bank && decide (u ≤ (finalZeroRows (e.query h) bank).card)

/-- Explicit instantiation of the generic epoch cardinal premise from the
actual finite-field adaptive theorem. No per-epoch probability is assumed. -/
theorem poolEpoch_local_count {s : ℕ} (e : PoolEpoch s H F I) (L u : ℕ)
    (hdepth : ∀ h, queryHeight (e.query h) ≤ L)
    (hnonzero : ∀ h bank, runOutput bank (e.query h) ≠ 0)
    (hfield : L+s < Fintype.card F) (h : H) :
    ((univ.filter fun bank => (e.toEpoch u).bad h bank = true).card : ℚ) ≤
      (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) *
        (Fintype.card (Fin s → I → F) : ℚ) := by
  have hb := uniform_pool_bad_fraction (e.query h) L u (hdepth h) (hnonzero h) hfield
  have hp : (0 : ℚ) < Fintype.card (Fin s → I → F) := Nat.cast_pos.mpr Fintype.card_pos
  have hc := (div_le_iff₀ hp).mp hb
  dsimp only [PoolEpoch.toEpoch]
  apply EpochComposition.designated_count_bound
    (fun bank => decide (u ≤ (finalZeroRows (e.query h) bank).card)) (e.invoke h)
  convert hc using 1 <;> congr 2
  congr 1
  ext bank
  simp

/-- Global bad-pool bound for a realized sequence of independently sampled
banks. Selection is among locally fixed final residuals, not retrospective
residual selection after observing future banks. -/
theorem concrete_epochs_bad_bound {s : ℕ}
    (epochs : List (PoolEpoch s H F I)) (L u : ℕ)
    (hdepth : ∀ e ∈ epochs, ∀ h, queryHeight (e.query h) ≤ L)
    (hnonzero : ∀ e ∈ epochs, ∀ h bank, runOutput bank (e.query h) ≠ 0)
    (hfield : L+s < Fintype.card F) (h : H) :
    EpochComposition.sampleProbability (epochs.map (fun e => e.toEpoch u)).length
      (EpochComposition.anyBad (epochs.map (fun e => e.toEpoch u)) h) ≤
      (epochs.length : ℚ) *
        (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) := by
  have hl : EpochComposition.LocalBounds
      (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u)
      (epochs.map (fun e => e.toEpoch u)) := by
    intro e he h
    obtain ⟨e0,he0,rfl⟩ := List.mem_map.mp he
    exact poolEpoch_local_count e0 L u (hdepth e0 he0) (hnonzero e0 he0) hfield h
  simpa using EpochComposition.anyBad_probability_le
    (epochs.map (fun e => e.toEpoch u)) _ hl h

#print axioms poolEpoch_local_count
#print axioms concrete_epochs_bad_bound
end ProgressivePool
