import FamilyAlgebra.ConcreteZeroLocus
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

namespace FamilyAlgebra

def f2Bit (z : ZMod 2) : Bool := decide (z ≠ 0)

theorem f2Bit_add (x y : ZMod 2) : f2Bit (x+y) = (f2Bit x ^^ f2Bit y) := by
  fin_cases x <;> fin_cases y <;> decide

theorem f2Bit_zero : f2Bit 0=false := by decide

theorem f2Bit_injective : Function.Injective f2Bit := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [f2Bit]

abbrev Parameters (n : Nat) := Fin (2*n+2) → ZMod 2

def paramRead {n : Nat} (p : Parameters n) (k : Nat) : Bool :=
  if h : k<2*n+2 then f2Bit (p ⟨k,h⟩) else false

theorem paramRead_add {n : Nat} (p q : Parameters n) (k : Nat) :
    paramRead (p+q) k = (paramRead p k ^^ paramRead q k) := by
  simp only [paramRead]
  split
  · simp only [Pi.add_apply, f2Bit_add]
  · rfl

theorem paramRead_zero {n : Nat} (k : Nat) : paramRead (0 : Parameters n) k=false := by
  simp [paramRead, f2Bit_zero]


/-- The six exceptional effective inputs: one of the six base tuples,
followed by zero in every extension coordinate. -/
def badParameters (n : Nat) (p : Parameters n) : Prop :=
  (paramRead p 0, paramRead p 1, paramRead p 2, paramRead p 3) ∈ sixBaseTuples ∧
    ∀ k : Fin (2*n+2), 4≤k.val → p k=0

/-- Canonical prefix projection; all remaining coordinates are padding. -/
def projectParameters (n : Nat) (positive : 0<n) (p : Fin (4*n) → ZMod 2) : Parameters n :=
  fun k => p ⟨k.val, by have := k.isLt; omega⟩

def badFullMask (n : Nat) (positive : 0<n) (p : Fin (4*n) → ZMod 2) : Prop :=
  badParameters n (projectParameters n positive p)

end FamilyAlgebra
