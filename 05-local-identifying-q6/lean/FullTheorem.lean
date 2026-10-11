import PathSemantics
import RUPPathFast.Chunk0193
namespace LocalIdentifyingQ6

theorem minimum_local_identifying_Q6 :
    (∃ C : Code, LocalIdentifying C ∧ cardinality C = 14) ∧
    (∀ C : Code, LocalIdentifying C → 14 ≤ cardinality C) :=
  minimum_fourteen_of_path_refutation Q6RUPPath.c92061

#print axioms minimum_local_identifying_Q6
end LocalIdentifyingQ6
