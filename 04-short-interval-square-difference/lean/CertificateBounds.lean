import LowerSoundness

/-!
Logical extraction of the upper-bound and finite-prefix certificates.
The checked Boolean computations are converted to propositions about
`Astra.count`; this module performs no further native evaluation.
-/

namespace Astra.Certificates

theorem upper144_facts_of_checked (hchecked : upper144Check = true) (n s : ℕ)
    (hn : IsUnit 144 n) (hs : s < 144) :
    (12 * count 144 n s 144 ≤ 144) ∧
      (∀ r < 144, 12 * count 144 n s r ≤ r + 21) ∧
      (∀ h < 147, count 144 n s h ≤ upperTarget h) := by
  have hc := (List.all_eq_true.mp hchecked) n
    (List.mem_range.mpr hn.1)
  simp only [if_pos hn] at hc
  have hcs := (List.all_eq_true.mp hc) s (List.mem_range.mpr hs)
  change
    ((decide (12 * count 144 n s 144 ≤ 144) &&
        (List.range 144).all (fun r =>
          decide (12 * count 144 n s r ≤ r + 21))) &&
      (List.range 147).all (fun h =>
        decide (count 144 n s h ≤ upperTarget h))) = true at hcs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hcs
  exact ⟨hcs.1.1, hcs.1.2, hcs.2⟩

private theorem upper144_facts (n s : ℕ)
    (hn : IsUnit 144 n) (hs : s < 144) :
    (12 * count 144 n s 144 ≤ 144) ∧
      (∀ r < 144, 12 * count 144 n s r ≤ r + 21) ∧
      (∀ h < 147, count 144 n s h ≤ upperTarget h) :=
  upper144_facts_of_checked upper144_checked n s hn hs

theorem upper144_period (n s : ℕ) (hn : IsUnit 144 n) (hs : s < 144) :
    12 * count 144 n s 144 ≤ 144 :=
  (upper144_facts n s hn hs).1

theorem upper144_remainder (n s r : ℕ)
    (hn : IsUnit 144 n) (hs : s < 144) (hr : r < 144) :
    12 * count 144 n s r ≤ r + 21 :=
  (upper144_facts n s hn hs).2.1 r hr

theorem upper144_finite (h n s : ℕ)
    (_hh1 : 1 ≤ h) (hh146 : h ≤ 146) (hn : IsUnit 144 n) (hs : s < 144) :
    count 144 n s h ≤ upperTarget h :=
  (upper144_facts n s hn hs).2.2 h (by omega)

theorem competitor_finite_of_checked (hchecked : finiteCheck = true) (m h : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144)
    (hh1 : 1 ≤ h) (hh146 : h ≤ 146) :
    ∃ n, IsUnit m n ∧ ∃ s, s < m ∧ upperTarget h ≤ count m n s h := by
  have hc := (List.all_eq_true.mp hchecked) m
    (List.mem_range.mpr (show m < 257 by omega))
  simp only [if_pos (And.intro hm1 hne)] at hc
  change
    ((List.range 146).all (fun i => decide (finiteN m (i + 1) ∈ usedNs m)) &&
      (usedNs m).all (fun n =>
        (List.range 146).all (fun i =>
          if finiteN m (i + 1) = n then
            decide (IsUnit m n ∧ finiteS m (i + 1) < m ∧
              upperTarget (i + 1) ≤ count m n (finiteS m (i + 1)) (i + 1))
          else true))) = true at hc
  simp only [Bool.and_eq_true] at hc
  have hp := hc
  have hi : h - 1 < 146 := by omega
  have hh : h - 1 + 1 = h := by omega
  have hnmem : finiteN m h ∈ usedNs m := by
    have hx := (List.all_eq_true.mp hp.1) (h - 1) (List.mem_range.mpr hi)
    simpa only [hh, decide_eq_true_eq] using hx
  have hncheck := (List.all_eq_true.mp hp.2) (finiteN m h) hnmem
  have hw := (List.all_eq_true.mp hncheck) (h - 1) (List.mem_range.mpr hi)
  simp only [hh, if_pos rfl, if_true, decide_eq_true_eq] at hw
  exact ⟨finiteN m h, hw.1, finiteS m h, hw.2.1, hw.2.2⟩

theorem competitor_finite (m h : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144)
    (hh1 : 1 ≤ h) (hh146 : h ≤ 146) :
    ∃ n, IsUnit m n ∧ ∃ s, s < m ∧ upperTarget h ≤ count m n s h :=
  competitor_finite_of_checked finite_checked m h hm1 hm256 hne hh1 hh146

end Astra.Certificates
