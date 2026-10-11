import LocalIdentifyingQ6
import Std.Sat.CNF
namespace LocalIdentifyingQ6
open Std.Sat

def edges : List (Vertex × Vertex) := vertices.flatMap fun u =>
  (vertices.filter fun v => adjacent u v && decide (u.val < v.val)).map fun v => (u,v)

def positiveClause (S : List Vertex) : CNF.Clause Nat := S.map fun v => (v.val+1, true)
def dominationClause (u : Vertex) : CNF.Clause Nat :=
  positiveClause (vertices.filter (closed u))
def separationClause (e : Vertex × Vertex) : CNF.Clause Nat :=
  positiveClause (vertices.filter fun x => closed e.1 x != closed e.2 x)
def graphCNF : CNF Nat := vertices.map dominationClause ++ edges.map separationClause

theorem vertices_complete (v : Vertex) : v ∈ vertices := by
  change v ∈ List.ofFn (fun x : Fin 64 => x)
  exact List.mem_ofFn.mpr ⟨v, rfl⟩

theorem positiveClause_sat (A : Nat → Bool) (C : Code)
    (hA : ∀ v : Vertex, A (v.val+1) = C v) (S : List Vertex) :
    CNF.Clause.eval A (positiveClause S) = true ↔ ∃ x, x ∈ S ∧ C x = true := by
  simp [positiveClause, CNF.Clause.eval, List.any_map, hA]

theorem dominationClause_sat (A : Nat → Bool) (C : Code)
    (hA : ∀ v : Vertex, A (v.val+1) = C v) (u : Vertex) :
    CNF.Clause.eval A (dominationClause u) = true ↔
      ∃ x, C x = true ∧ closed u x = true := by
  rw [dominationClause, positiveClause_sat A C hA]
  simp only [List.mem_filter, vertices_complete, true_and]
  constructor <;> rintro ⟨x, hx, hy⟩ <;> exact ⟨x, hy, hx⟩

theorem separationClause_sat (A : Nat → Bool) (C : Code)
    (hA : ∀ v : Vertex, A (v.val+1) = C v) (u v : Vertex) :
    CNF.Clause.eval A (separationClause (u,v)) = true ↔ EdgeHit C u v := by
  rw [separationClause, positiveClause_sat A C hA]
  simp only [List.mem_filter, vertices_complete, true_and, bne_iff_ne, EdgeHit]
  constructor <;> rintro ⟨x, hx, hy⟩ <;> exact ⟨x, hy, hx⟩

theorem constraints_graph_sat (A : Nat → Bool) (C : Code)
    (hA : ∀ v : Vertex, A (v.val+1) = C v) (h : Constraints C) :
    graphCNF.Sat A := by
  simp only [CNF.Sat, graphCNF, CNF.eval_append, Bool.and_eq_true]
  constructor
  · simp only [CNF.eval, List.all_map, List.all_eq_true]
    intro u _
    exact (dominationClause_sat A C hA u).mpr (h.1 u)
  · simp only [CNF.eval, List.all_map, List.all_eq_true]
    intro e he
    simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter,
      Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨u, _, v, ⟨_, hadj, _⟩, he⟩ := he
    subst e
    exact (separationClause_sat A C hA u v).mpr (h.2 u v hadj)


theorem adjacent_symmetric (u v : Vertex) : adjacent u v = adjacent v u := by
  unfold adjacent
  change [1, 2, 4, 8, 16, 32].contains (u.val ^^^ v.val) = [1, 2, 4, 8, 16, 32].contains (v.val ^^^ u.val)
  rw [Nat.xor_comm]

theorem graph_sat_constraints (A : Nat → Bool) (C : Code)
    (hA : ∀ v : Vertex, A (v.val+1) = C v) (h : graphCNF.Sat A) :
    Constraints C := by
  unfold CNF.Sat at h
  rw [graphCNF, CNF.eval_append, Bool.and_eq_true] at h
  simp only [CNF.eval, List.all_map, List.all_eq_true] at h
  constructor
  · intro u
    exact (dominationClause_sat A C hA u).mp (h.1 u (vertices_complete u))
  · intro u v huv
    have he : u ≠ v := by
      intro heq
      subst v
      have hh : adjacent u u = false := by
        unfold adjacent
        change [1, 2, 4, 8, 16, 32].contains (u.val ^^^ u.val) = false
        simp
      simp [hh] at huv
    have ordered : ∀ u v : Vertex, adjacent u v = true → u.val < v.val → EdgeHit C u v := by
      intro u v hadj hlt
      apply (separationClause_sat A C hA u v).mp
      apply h.2 (u,v)
      simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter,
        Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨u, vertices_complete u, v, ⟨vertices_complete v, hadj, hlt⟩, rfl⟩
    by_cases hlt : u.val < v.val
    · exact ordered u v huv hlt
    · have hgt : v.val < u.val := by
        have hne : u.val ≠ v.val := fun hh => he (Fin.ext hh)
        omega
      have hvu : adjacent v u = true := (adjacent_symmetric v u).trans huv
      obtain ⟨x, hx, hd⟩ := ordered v u hvu hgt
      exact ⟨x, hx, Ne.symm hd⟩

theorem localIdentifying_iff_graph_sat (A : Nat → Bool) (C : Code)
    (hA : ∀ v : Vertex, A (v.val+1) = C v) :
    LocalIdentifying C ↔ graphCNF.Sat A := by
  rw [localIdentifying_iff_constraints]
  exact ⟨constraints_graph_sat A C hA, graph_sat_constraints A C hA⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem edge_count : edges.length = 192 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_clause_count : graphCNF.length = 256 := by decide +kernel

#print axioms constraints_graph_sat
end LocalIdentifyingQ6
