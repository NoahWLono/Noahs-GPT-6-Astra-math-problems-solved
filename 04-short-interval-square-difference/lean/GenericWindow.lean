import Mathlib.Tactic

/-!
Generic finite-to-all-length window lemmas.  These lemmas do not assume any
facts about square residues or a computed minimax table.  Their finite
hypotheses are intended to be discharged by the separate certificate module.
-/

namespace Astra.GenericWindow

/-- Number (or weight) of selected positions in a window. -/
def window (f : ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => window f s h + f (s + h)

theorem window_add (f : ℕ → ℕ) (s a b : ℕ) :
    window f s (a + b) = window f s a + window f (s + a) b := by
  induction b with
  | zero => simp [window]
  | succ b ih => simp [window, ih, Nat.add_assoc]

theorem window_period_shift (f : ℕ → ℕ) (p : ℕ)
    (hf : ∀ x, f (x + p) = f x) (s h : ℕ) :
    window f (s + p) h = window f s h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [window, ih]
    have he : s + p + h = (s + h) + p := by omega
    rw [he, hf]

/-- Split a window into complete periods and a remainder at the same start. -/
theorem window_period_blocks (f : ℕ → ℕ) (p : ℕ)
    (hf : ∀ x, f (x + p) = f x) (s q r : ℕ) :
    window f s (q * p + r) = q * window f s p + window f s r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : (q + 1) * p + r = p + (q * p + r) := by ring
    rw [he, window_add, window_period_shift f p hf, ih]
    ring

theorem window_div_mod (f : ℕ → ℕ) (p : ℕ)
    (hf : ∀ x, f (x + p) = f x) (s h : ℕ) :
    window f s h = (h / p) * window f s p + window f s (h % p) := by
  have he : (h / p) * p + h % p = h := by
    simpa [Nat.mul_comm] using Nat.div_add_mod h p
  simpa only [he] using window_period_blocks f p hf s (h / p) (h % p)

/-- A finite period bound and remainder excess bound imply a global bound. -/
theorem window_upper_of_remainders (f : ℕ → ℕ) (p : ℕ)
    (hp : 0 < p) (hf : ∀ x, f (x + p) = f x)
    (s scale slope excess : ℕ)
    (hperiod : scale * window f s p ≤ slope * p)
    (hremainder : ∀ r < p, scale * window f s r ≤ slope * r + excess)
    (h : ℕ) : scale * window f s h ≤ slope * h + excess := by
  have hr := hremainder (h % p) (Nat.mod_lt h hp)
  have hq := Nat.mul_le_mul_left (h / p) hperiod
  have hd : (h / p) * p + h % p = h := by
    simpa [Nat.mul_comm] using Nat.div_add_mod h p
  rw [window_div_mod f p hf s h]
  calc
    scale * ((h / p) * window f s p + window f s (h % p))
        = (h / p) * (scale * window f s p) + scale * window f s (h % p) := by ring
    _ ≤ (h / p) * (slope * p) + (slope * (h % p) + excess) :=
      Nat.add_le_add hq hr
    _ = slope * h + excess := by
      calc
        _ = slope * ((h / p) * p + h % p) + excess := by ring
        _ = slope * h + excess := by rw [hd]

/-- A fixed start's finite period and remainder lower bounds extend globally. -/
theorem window_lower_of_remainders (f : ℕ → ℕ) (p : ℕ)
    (hp : 0 < p) (hf : ∀ x, f (x + p) = f x)
    (s scale slope : ℕ)
    (hperiod : slope * p ≤ scale * window f s p)
    (hremainder : ∀ r < p, slope * r ≤ scale * window f s r)
    (h : ℕ) : slope * h ≤ scale * window f s h := by
  have hr := hremainder (h % p) (Nat.mod_lt h hp)
  have hq := Nat.mul_le_mul_left (h / p) hperiod
  have hd : (h / p) * p + h % p = h := by
    simpa [Nat.mul_comm] using Nat.div_add_mod h p
  rw [window_div_mod f p hf s h]
  calc
    slope * h = (h / p) * (slope * p) + slope * (h % p) := by
      calc
        _ = slope * ((h / p) * p + h % p) := by rw [hd]
        _ = _ := by ring
    _ ≤ (h / p) * (scale * window f s p) + scale * window f s (h % p) :=
      Nat.add_le_add hq hr
    _ = scale * ((h / p) * window f s p + window f s (h % p)) := by ring

/-- Starts may vary with the remainder; no one start must work for all lengths. -/
theorem exists_window_lower_of_remainders (f : ℕ → ℕ) (p : ℕ)
    (hp : 0 < p) (hf : ∀ x, f (x + p) = f x)
    (scale slope : ℕ)
    (hperiod : ∀ s < p, slope * p ≤ scale * window f s p)
    (hremainder : ∀ r < p, ∃ s < p, slope * r ≤ scale * window f s r)
    (h : ℕ) : ∃ s < p, slope * h ≤ scale * window f s h := by
  obtain ⟨s, hs, hr⟩ := hremainder (h % p) (Nat.mod_lt h hp)
  refine ⟨s, hs, ?_⟩
  have hq := Nat.mul_le_mul_left (h / p) (hperiod s hs)
  have hd : (h / p) * p + h % p = h := by
    simpa [Nat.mul_comm] using Nat.div_add_mod h p
  rw [window_div_mod f p hf s h]
  calc
    slope * h = (h / p) * (slope * p) + slope * (h % p) := by
      calc
        _ = slope * ((h / p) * p + h % p) := by rw [hd]
        _ = _ := by ring
    _ ≤ (h / p) * (scale * window f s p) + scale * window f s (h % p) :=
      Nat.add_le_add hq hr
    _ = scale * ((h / p) * window f s p + window f s (h % p)) := by ring

/-- The scaled bounds used by the 144-versus-competitor tail comparison. -/
theorem compare_from_147 (h upper lower : ℕ) (hh : 147 ≤ h)
    (hu : 12 * upper ≤ h + 21) (hl : 2 * h ≤ 21 * lower) :
    upper ≤ lower := by
  omega

/-- The same density separation is strict from length 148 onward. -/
theorem compare_strict_from_148 (h upper lower : ℕ) (hh : 148 ≤ h)
    (hu : 12 * upper ≤ h + 21) (hl : 2 * h ≤ 21 * lower) :
    upper < lower := by
  omega

/-- Combine a finite prefix with the independently certified density tail. -/
theorem compare_all_lengths (upper lower : ℕ → ℕ)
    (hfinite : ∀ h < 147, upper h ≤ lower h)
    (hu : ∀ h, 12 * upper h ≤ h + 21)
    (hl : ∀ h, 2 * h ≤ 21 * lower h) :
    ∀ h, upper h ≤ lower h := by
  intro h
  by_cases hh : h < 147
  · exact hfinite h hh
  · exact compare_from_147 h (upper h) (lower h) (by omega) (hu h) (hl h)

end Astra.GenericWindow
