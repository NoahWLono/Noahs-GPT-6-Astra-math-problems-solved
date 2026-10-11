import CertificateBounds
import SemanticBridge

/-!
The unconditional all-length theorem. The finite certificates are evaluated
inside Lean; this file does not read or assume a Python result table.
-/

namespace Astra

open Certificates

/-- The period and remainder certificates give the uniform discrepancy bound. -/
theorem upper144_all_lengths (h : ℕ) : 12 * F 144 h ≤ h + 21 := by
  apply F_scaled_le_of_counts
  intro n hn s hs
  simpa only [count, one_mul] using
    GenericWindow.window_upper_of_remainders
      (indicator 144 n) 144 (by omega) (indicator_period 144 n)
      s 12 1 21
      (by simpa only [count, one_mul] using upper144_period n s hn hs)
      (by intro r hr
          simpa only [count, one_mul] using upper144_remainder n s r hn hs hr)
      h

/-- A certified input residue supplies the lower density bound at all lengths. -/
theorem competitor_all_lengths (m h : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144) :
    2 * h ≤ 21 * F m h := by
  have hn : IsUnit m (lowerN m) := lower_unit m hm1 hm256 hne
  obtain ⟨s, hs, hcount⟩ :=
    GenericWindow.exists_window_lower_of_remainders
      (indicator m (lowerN m)) m (by omega) (indicator_period m (lowerN m))
      21 2
      (by intro s hs
          exact lower_period m s hm1 hm256 hne hs)
      (by intro r hr
          exact lower_remainder m r hm1 hm256 hne hr)
      h
  have hmax : count m (lowerN m) s h ≤ F m h := count_le_F hn hs
  change 2 * h ≤ 21 * count m (lowerN m) s h at hcount
  omega

/-- The finite prefix is certified with actual upper and lower window counts. -/
theorem finite_prefix_optimal (m h : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144)
    (hh1 : 1 ≤ h) (hh146 : h ≤ 146) : F 144 h ≤ F m h := by
  have hu : F 144 h ≤ upperTarget h := by
    apply F_le_of_counts
    intro n hn s hs
    exact upper144_finite h n s hh1 hh146 hn hs
  obtain ⟨n, hn, s, hs, hl⟩ := competitor_finite m h hm1 hm256 hne hh1 hh146
  exact hu.trans (hl.trans (count_le_F hn hs))

/-- Main theorem: modulus 144 is optimal for all natural lengths, including zero. -/
theorem uniform_optimal (m h : ℕ) (hm1 : 1 ≤ m) (hm256 : m ≤ 256) :
    F 144 h ≤ F m h := by
  by_cases hsame : m = 144
  · subst m
    exact le_rfl
  by_cases hzero : h = 0
  · subst h
    simp only [F_zero_length, le_refl]
  by_cases hfinite : h ≤ 146
  · exact finite_prefix_optimal m h hm1 hm256 hsame (by omega) hfinite
  · exact GenericWindow.compare_from_147 h (F 144 h) (F m h) (by omega)
      (upper144_all_lengths h) (competitor_all_lengths m h hm1 hm256 hsame)

/-- The formal argument also proves unique optimality for each length ≥ 148. -/
theorem strict_optimal_from_148 (m h : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144) (hh : 148 ≤ h) :
    F 144 h < F m h :=
  GenericWindow.compare_strict_from_148 h (F 144 h) (F m h) hh
    (upper144_all_lengths h) (competitor_all_lengths m h hm1 hm256 hne)

end Astra

#check Astra.uniform_optimal
#check Astra.strict_optimal_from_148
#print axioms Astra.uniform_optimal
#print axioms Astra.strict_optimal_from_148
#print axioms Astra.upper144_all_lengths
#print axioms Astra.competitor_all_lengths
#print axioms Astra.indicator_eq_one_iff
#print axioms Astra.count_eq_sum_congruence
#print axioms Astra.F_eq_sup_congruence
