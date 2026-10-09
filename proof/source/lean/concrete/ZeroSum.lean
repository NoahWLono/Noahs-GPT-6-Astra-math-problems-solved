import InputCombination
import QuadraticWalshShift
namespace FastWalsh

def sumTree : Tree n → Int
  | .leaf z => z
  | .node l r => sumTree l + sumTree r

theorem sumTree_tabulate (f : BitVec n → Int) : sumTree (tabulate f) = sumDomain f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tabulate, sumTree, sumDomain, ih]

theorem componentZeroSum_eq_sumTree (cs : List (Nat × Nat × BitVec m)) (b : BitVec m) :
    QuadraticWalshShift.componentZeroSum n cs b = sumTree (signTree (quadratic cs : BitVec n → BitVec m) b) := by
  rw [signTree, sumTree_tabulate]
  simp only [quadratic_component_correct, QuadraticWalshShift.componentZeroSum]

#print axioms componentZeroSum_eq_sumTree
end FastWalsh
