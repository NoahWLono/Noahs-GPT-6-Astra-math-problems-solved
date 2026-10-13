module

public import Q7Mod.Integration.ExactQ7

public section

-- Explicit type ascription prevents a renamed or weakened predicate interface.
example :
    (∃ C : ExactCubeCodes.Code 7,
      ExactCubeCodes.LocalIdentifying C ∧ ExactCubeCodes.cardinality C = 24) ∧
    (∀ C : ExactCubeCodes.Code 7,
      ExactCubeCodes.LocalIdentifying C → 24 ≤ ExactCubeCodes.cardinality C) :=
  ExactCubeCodes.localIdentifying_Q7_optimum24

#check ExactCubeCodes.LocalIdentifying
#check ExactCubeCodes.localIdentifying_Q7_optimum24
#print axioms ExactCubeCodes.localIdentifying_Q7_optimum24
run_cmd do
  let env ← Lean.getEnv
  match env.find? `ExactCubeCodes.localIdentifying_Q7_optimum24 with
  | some (.axiomInfo _) => pure ()
  | _ => throwError "expected checked body-hidden optimum interface"
