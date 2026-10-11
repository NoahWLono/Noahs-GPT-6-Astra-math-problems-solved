import Model
import WindowScan
import WitnessData

/-!
Finite certificates for the raw square-residue model. WitnessData contains
untrusted integer literals. Native evaluation checks the modular predicates;
no Python result or certificate is assumed as a mathematical axiom.
-/

namespace Astra.Certificates

open Astra.GenericWindow

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Explicit envelope; its upper-bound property is checked below. -/
def upperTarget (h : ℕ) : ℕ :=
  max (4 * (h / 72) + (if 1 ≤ h % 72 then 1 else 0) +
    (if 3 ≤ h % 72 then 1 else 0) + (if 19 ≤ h % 72 then 1 else 0) +
    (if 27 ≤ h % 72 then 1 else 0))
    (2 * (h / 24) + (if 1 ≤ h % 24 then 1 else 0) +
      (if 7 ≤ h % 24 then 1 else 0))

def lowerN (m : ℕ) : ℕ := ((lowerWitnessData[m]?).getD (0, #[])).1

def lowerS (m r : ℕ) : ℕ :=
  ((((lowerWitnessData[m]?).getD (0, #[])).2)[r]?).getD 0

def finiteN (m h : ℕ) : ℕ :=
  ((((finiteWitnessData[m]?).getD #[])[h - 1]?).getD (0, 0)).1

def finiteS (m h : ℕ) : ℕ :=
  ((((finiteWitnessData[m]?).getD #[])[h - 1]?).getD (0, 0)).2

def usedNs (m : ℕ) : List ℕ :=
  (((finiteWitnessData[m]?).getD #[]).toList.map Prod.fst).eraseDups

/-- Build one mask per unit n and reuse it for every start and length. -/
def upper144Check : Bool :=
  (List.range 144).all fun n =>
    if IsUnit 144 n then
      let bits := mask 144 n
      let f := fun a => (bits[a % 144]?).getD 0
      (List.range 144).all fun s =>
        decide (12 * window f s 144 ≤ 144) &&
        ((List.range 144).all fun r => decide (12 * window f s r ≤ r + 21)) &&
        ((List.range 147).all fun h => decide (window f s h ≤ upperTarget h))
    else true

/-- Each competitor has a fixed unit n and certified remainder starts. -/
def lowerCheck : Bool :=
  (List.range 257).all fun m =>
    if 1 ≤ m ∧ m ≠ 144 then
      let n := lowerN m
      let bits := mask m n
      let f := fun a => (bits[a % m]?).getD 0
      decide (IsUnit m n) &&
      ((List.range m).all fun s => decide (2 * m ≤ 21 * window f s m)) &&
      ((List.range m).all fun r =>
        decide (lowerS m r < m ∧ 2 * r ≤ 21 * window f (lowerS m r) r))
    else true

/-- Cache only masks used by the supplied finite witnesses. -/
def finiteCheck : Bool :=
  (List.range 257).all fun m =>
    if 1 ≤ m ∧ m ≠ 144 then
      let ns := usedNs m
      ((List.range 146).all fun i => decide (finiteN m (i + 1) ∈ ns)) &&
      (ns.all fun n =>
        let bits := mask m n
        let f := fun a => (bits[a % m]?).getD 0
        (List.range 146).all fun i =>
          if finiteN m (i + 1) = n then
            decide (IsUnit m n ∧ finiteS m (i + 1) < m ∧
              upperTarget (i + 1) ≤ window f (finiteS m (i + 1)) (i + 1))
          else true)
    else true

private theorem all_range_get {N i : ℕ} {p : ℕ → Bool}
    (h : (List.range N).all p = true) (hi : i < N) : p i = true :=
  (List.all_eq_true.mp h) i (List.mem_range.mpr hi)

/-- Running sums compute exactly the same exhaustive upper predicate. -/
def upper144FastCheck : Bool :=
  (List.range 144).all fun n =>
    if IsUnit 144 n then
      let bits := mask 144 n
      let f := fun a => (bits[a % 144]?).getD 0
      (List.range 144).all fun s =>
        decide (12 * window f s 144 ≤ 144) &&
        (windowScan f s (fun r c => decide (12 * c ≤ r + 21)) 144).2 &&
        (windowScan f s (fun h c => decide (c ≤ upperTarget h)) 147).2
    else true

theorem upper144_fast_correct : upper144FastCheck = upper144Check := by
  simp only [upper144FastCheck, upper144Check, windowScan_snd]

/-- Uses Lean's explicitly disclosed native Boolean evaluator. -/
theorem upper144_checked : upper144Check = true := by
  rw [← upper144_fast_correct]
  native_decide

/-- Uses Lean's explicitly disclosed native Boolean evaluator. -/
theorem lower_checked : lowerCheck = true := by native_decide

/-- Uses Lean's explicitly disclosed native Boolean evaluator. -/
theorem finite_checked : finiteCheck = true := by native_decide

end Astra.Certificates
