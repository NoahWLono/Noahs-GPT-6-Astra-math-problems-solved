import GenericWindow

/-!
A linear scan that checks a predicate of every prefix count.  The proofs
show equality to independently recomputing each window in the original
finite checker; the optimization changes only evaluation cost.
-/

namespace Astra.GenericWindow

def windowScan (f : ℕ → ℕ) (s : ℕ) (P : ℕ → ℕ → Bool) : ℕ → ℕ × Bool
  | 0 => (0, true)
  | h + 1 =>
      let previous := windowScan f s P h
      (previous.1 + f (s + h), previous.2 && P h previous.1)

theorem windowScan_eq (f : ℕ → ℕ) (s : ℕ) (P : ℕ → ℕ → Bool) (H : ℕ) :
    windowScan f s P H =
      (window f s H, (List.range H).all (fun h => P h (window f s h))) := by
  induction H with
  | zero => rfl
  | succ H ih =>
    simp [windowScan, ih, window, List.range_succ]

theorem windowScan_fst (f : ℕ → ℕ) (s : ℕ) (P : ℕ → ℕ → Bool) (H : ℕ) :
    (windowScan f s P H).1 = window f s H := by
  rw [windowScan_eq]

theorem windowScan_snd (f : ℕ → ℕ) (s : ℕ) (P : ℕ → ℕ → Bool) (H : ℕ) :
    (windowScan f s P H).2 =
      (List.range H).all (fun h => P h (window f s h)) := by
  rw [windowScan_eq]

theorem windowScan_snd_eq_true_iff
    (f : ℕ → ℕ) (s : ℕ) (P : ℕ → ℕ → Bool) (H : ℕ) :
    (windowScan f s P H).2 = true ↔
      ∀ h < H, P h (window f s h) = true := by
  rw [windowScan_snd]
  simp [List.all_eq_true, List.mem_range]

end Astra.GenericWindow
