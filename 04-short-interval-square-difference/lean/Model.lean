import GenericWindow
import Mathlib.Data.Finset.Lattice.Fold

/-!
The square-difference mask model.  Congruences are expressed as
`a² = n + b² (mod m)` to avoid truncated subtraction on natural numbers.
Zero is included among the square residues.  The maximum is taken over
all unit residues and all starts, with repeated positions counted when a
window is longer than its period.
-/

namespace Astra

def mask (m n : ℕ) : Array ℕ :=
  ((List.range m).map (fun a =>
    if (List.range m).any (fun b => a * a % m == (n + b * b) % m)
    then 1 else 0)).toArray

def indicator (m n a : ℕ) : ℕ := (mask m n)[a % m]?.getD 0

def count (m n s h : ℕ) : ℕ :=
  GenericWindow.window (indicator m n) s h

def IsUnit (m n : ℕ) : Prop := n < m ∧ Nat.gcd n m = 1

instance (m n : ℕ) : Decidable (IsUnit m n) :=
  inferInstanceAs (Decidable (n < m ∧ Nat.gcd n m = 1))

def F (m h : ℕ) : ℕ :=
  (Finset.range m).sup (fun n =>
    if Nat.gcd n m = 1 then
      (Finset.range m).sup (fun s => count m n s h)
    else 0)

theorem indicator_period (m n x : ℕ) :
    indicator m n (x + m) = indicator m n x := by
  simp [indicator]

theorem indicator_eq_one_iff (m n a : ℕ) (hm : 0 < m) :
    indicator m n a = 1 ↔
      ∃ b < m, a * a % m = (n + b * b) % m := by
  have ha : a % m < m := Nat.mod_lt a hm
  simp [indicator, mask, List.getElem?_range ha, Nat.mul_mod]

theorem count_le_F {m n s h : ℕ} (hn : IsUnit m n) (hs : s < m) :
    count m n s h ≤ F m h := by
  have hstart : count m n s h ≤
      (Finset.range m).sup (fun s => count m n s h) :=
    Finset.le_sup (f := fun s => count m n s h) (Finset.mem_range.mpr hs)
  apply hstart.trans
  have hunit := Finset.le_sup
    (f := fun n => if Nat.gcd n m = 1 then
      (Finset.range m).sup (fun s => count m n s h) else 0)
    (Finset.mem_range.mpr hn.1)
  simpa only [hn.2, if_true, F] using hunit

theorem F_le_of_counts {m h b : ℕ}
    (hb : ∀ n, IsUnit m n → ∀ s < m, count m n s h ≤ b) :
    F m h ≤ b := by
  unfold F
  apply Finset.sup_le
  intro n hn
  split_ifs with hg
  · apply Finset.sup_le
    intro s hs
    exact hb n ⟨Finset.mem_range.mp hn, hg⟩ s (Finset.mem_range.mp hs)
  · exact Nat.zero_le b

theorem F_scaled_le_of_counts {m h scale b : ℕ}
    (hb : ∀ n, IsUnit m n → ∀ s < m, scale * count m n s h ≤ b) :
    scale * F m h ≤ b := by
  by_cases hs : scale = 0
  · simp [hs]
  · have hbound : F m h ≤ b / scale := by
      apply F_le_of_counts
      intro n hn s hsm
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hs)).mpr
        (by simpa [Nat.mul_comm] using hb n hn s hsm)
    calc
      scale * F m h ≤ scale * (b / scale) := Nat.mul_le_mul_left scale hbound
      _ ≤ b := by simpa [Nat.mul_comm] using Nat.div_mul_le_self b scale

end Astra
