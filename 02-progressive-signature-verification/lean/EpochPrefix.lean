import EpochComposition

/-!
# Prefix measurability and deferred sampling

The all-banks-upfront finite product has exactly the same prefix/current-bank
masses as drawing a fresh independent uniform bank after each incoming history.
The incoming history and each designated candidate are determined from past
banks and the current bank.  A later selector can choose among those fixed
candidates; it cannot retroactively change an epoch's residual or bad predicate.
-/
namespace ProgressivePool.EpochComposition
open Finset Classical
universe u v
variable {B : Type u} {H : Type v}

/-- Concatenate explicit sample products for two consecutive epoch lists. -/
def appendDraws : (pre post : List (Epoch H B)) →
    Samples B pre.length → Samples B post.length → Samples B (pre ++ post).length
  | [], _, _, future => future
  | _ :: pre, post, draws, future =>
      (draws.1, appendDraws pre post draws.2 future)

/-- Incoming state after the prefix; no future bank is an argument. -/
def afterPrefix : (pre : List (Epoch H B)) → H → Samples B pre.length → H
  | [], h, _ => h
  | e :: pre, h, draws => afterPrefix pre (e.next h draws.1) draws.2

/-- State visible before the indexed epoch, or the final state past the end. -/
def historyAt : (epochs : List (Epoch H B)) → H → Samples B epochs.length → ℕ → H
  | [], h, _, _ => h
  | _ :: _, h, _, 0 => h
  | e :: es, h, draws, n + 1 => historyAt es (e.next h draws.1) draws.2 n

/-- In the complete run, the boundary history depends only on the prefix. -/
theorem historyAt_append_prefix (pre post : List (Epoch H B)) (h : H)
    (past : Samples B pre.length) (future : Samples B post.length) :
    historyAt (pre ++ post) h (appendDraws pre post past future) pre.length =
      afterPrefix pre h past := by
  induction pre generalizing h with
  | nil => cases post <;> rfl
  | cons e pre ih =>
      exact ih (e.next h past.1) past.2

/-- The current designated candidate cannot depend on later epoch banks. -/
theorem badAt_append_current (pre post : List (Epoch H B)) (e : Epoch H B)
    (h : H) (past : Samples B pre.length) (bank : B)
    (future : Samples B post.length) :
    badAt (pre ++ e :: post) h (appendDraws pre (e :: post) past (bank, future))
      pre.length = e.bad (afterPrefix pre h past) bank := by
  induction pre generalizing h with
  | nil => rfl
  | cons e' pre ih => exact ih (e'.next h past.1) past.2

/-- Changing all later banks cannot change the already fixed candidate bit. -/
theorem candidate_future_independent (pre post : List (Epoch H B)) (e : Epoch H B)
    (h : H) (past : Samples B pre.length) (bank : B)
    (future₁ future₂ : Samples B post.length) :
    badAt (pre ++ e :: post) h (appendDraws pre (e :: post) past (bank, future₁)) pre.length =
    badAt (pre ++ e :: post) h (appendDraws pre (e :: post) past (bank, future₂)) pre.length := by
  rw [badAt_append_current, badAt_append_current]

variable [Fintype B] [Nonempty B]

/-- The exact finite product weight splits into past and future factors. -/
theorem sampleWeight_append (pre post : List (Epoch H B))
    (past : Samples B pre.length) (future : Samples B post.length) :
    sampleWeight (pre ++ post).length (appendDraws pre post past future) =
      sampleWeight pre.length past * sampleWeight post.length future := by
  induction pre with
  | nil => simp [appendDraws, sampleWeight]
  | cons e pre ih =>
      change (1 / (Fintype.card B : ℚ)) *
        sampleWeight (pre ++ post).length (appendDraws pre post past.2 future) = _
      rw [ih]
      simp [sampleWeight, mul_assoc]

/-- Marginalizing every later bank leaves precisely `pastWeight / card(B)`
for each current bank, regardless of the incoming history.  Together with
`historyAt_append_prefix`, this is the deferred fresh-sampling refinement. -/
theorem current_bank_uniform_given_prefix (pre post : List (Epoch H B))
    (e : Epoch H B) (past : Samples B pre.length) (bank : B) :
    (∑ future : Samples B post.length,
      sampleWeight (pre ++ e :: post).length
        (appendDraws pre (e :: post) past (bank, future))) =
      sampleWeight pre.length past / (Fintype.card B : ℚ) := by
  simp only [sampleWeight_append]
  change (∑ future : Samples B post.length,
    sampleWeight pre.length past *
      ((1 / (Fintype.card B : ℚ)) * sampleWeight post.length future)) = _
  simp [← mul_sum, sampleWeight_sum, div_eq_mul_inv]

#print axioms historyAt_append_prefix
#print axioms badAt_append_current
#print axioms candidate_future_independent
#print axioms sampleWeight_append
#print axioms current_bank_uniform_given_prefix
end ProgressivePool.EpochComposition
