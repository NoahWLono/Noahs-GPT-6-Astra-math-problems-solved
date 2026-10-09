import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace QuadraticFourRaw
open scoped BigOperators
abbrev F := ZMod 2
abbrev V := Fin 4 → F

def poly (a b c d e f g h i j k : F) (x : V) : F :=
  a + b*x 0 + c*x 1 + d*x 2 + e*x 3 + f*x 0*x 1 +
    g*x 0*x 2 + h*x 0*x 3 + i*x 1*x 2 + j*x 1*x 3 + k*x 2*x 3

def weight (f : V → F) : ℕ := ∑ x, (f x).val

theorem weights000000 : ∀ g h i j k : F,
    weight (poly 0 0 0 0 0 0 g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by decide
end QuadraticFourRaw
