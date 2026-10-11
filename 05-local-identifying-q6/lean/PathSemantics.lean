import PathInputs
import CardinalityBridge
import NormalizeSmallCode
namespace LocalIdentifyingQ6
open CardinalityEncoding

def pathInput (C : Code) (n : Nat) : Bool :=
  if h : n - 1 < 64 then C ⟨n-1, h⟩ else false

theorem pathInput_vertex (C : Code) (v : Vertex) :
    pathInput C (v.val+1) = C v := by
  simp [pathInput, v.isLt]

theorem small_normalized_path_inputs (C : Code) (h : LocalIdentifying C)
    (h0 : C 0 = true) (h1 : C 1 = true) (h2 : C 2 = true)
    (hs : cardinality C ≤ 13) :
    Q6RUPPath.Inputs (fun n => assignment (pathInput C) n = true) := by
  apply path_inputs_from_constraints C (pathInput C) (pathInput_vertex C)
    ((localIdentifying_iff_constraints C).mp h) h0 h1 h2
  rw [prefixCount_eq_cardinality C (pathInput C) (pathInput_vertex C)]
  exact hs

theorem lower_bound_of_path_refutation
    (refute : ∀ p : Nat → Prop, Q6RUPPath.Inputs p → False)
    (C : Code) (h : LocalIdentifying C) : 14 ≤ cardinality C := by
  apply Classical.byContradiction
  intro hsmall
  have hs : cardinality C ≤ 13 := by omega
  obtain ⟨D, hd, h0, h1, h2, hcard⟩ := normalize_small_code_path C h hs
  exact refute _ (small_normalized_path_inputs D hd h0 h1 h2 (hcard ▸ hs))

/-- The concrete refutation must be supplied by the checked RUP proof modules. -/
theorem minimum_fourteen_of_path_refutation
    (refute : ∀ p : Nat → Prop, Q6RUPPath.Inputs p → False) :
    (∃ C : Code, LocalIdentifying C ∧ cardinality C = 14) ∧
    (∀ C : Code, LocalIdentifying C → 14 ≤ cardinality C) := by
  exact ⟨⟨witness, witness_localIdentifying, witness_cardinality⟩,
    lower_bound_of_path_refutation refute⟩

#print axioms small_normalized_path_inputs
#print axioms minimum_fourteen_of_path_refutation
end LocalIdentifyingQ6
