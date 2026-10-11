import Translation

namespace LocalIdentifyingQ6

def CodePath (C : Code) : Prop :=
  ∃ c a b : Vertex, C c = true ∧ C a = true ∧ C b = true ∧
    adjacent c a = true ∧ adjacent c b = true ∧ a ≠ b

def Independent (C : Code) : Prop :=
  ∀ a b, C a = true → C b = true → adjacent a b = false

theorem cube_adjacent_symm (a b : Vertex) : adjacent a b = adjacent b a := by
  unfold adjacent
  change [1, 2, 4, 8, 16, 32].contains (a.val ^^^ b.val) = _
  rw [Nat.xor_comm]
  rfl

theorem cube_adjacent_irrefl (a : Vertex) : adjacent a a = false := by
  unfold adjacent
  change [1, 2, 4, 8, 16, 32].contains (a.val ^^^ a.val) = false
  simp

theorem cube_closed_self (a : Vertex) : closed a a = true := by simp [closed]

theorem cube_closed_of_adjacent {a b : Vertex} (h : adjacent a b = true) : closed a b = true := by
  simp [closed, h]

theorem cube_adjacent_of_closed {a b : Vertex} (h : closed a b = true) (hne : a ≠ b) :
    adjacent a b = true := by
  simpa [closed, hne] using h

theorem no_path_independent (C : Code) (hc : LocalIdentifying C) (hn : ¬ CodePath C) :
    Independent C := by
  intro a b ha hb
  cases he : adjacent a b
  · rfl
  · exfalso
    have hs := (localIdentifying_iff_constraints C).mp hc
    obtain ⟨x, hx, hd⟩ := hs.2 a b he
    have hab := cube_closed_of_adjacent he
    have hba := cube_closed_of_adjacent ((cube_adjacent_symm b a).trans he)
    have hxa : x ≠ a := by intro h; subst x; exact hd ((cube_closed_self a).trans hba.symm)
    have hxb : x ≠ b := by intro h; subst x; exact hd (hab.trans (cube_closed_self b).symm)
    cases hax : closed a x <;> cases hbx : closed b x
    · exact hd (hax.trans hbx.symm)
    · exact hn ⟨b, a, x, hb, ha, hx, (cube_adjacent_symm b a).trans he,
        cube_adjacent_of_closed hbx (Ne.symm hxb), Ne.symm hxa⟩
    · exact hn ⟨a, b, x, ha, hb, hx, he,
        cube_adjacent_of_closed hax (Ne.symm hxa), Ne.symm hxb⟩
    · exact hd (hax.trans hbx.symm)

theorem independent_outside_two (C : Code) (hc : LocalIdentifying C) (hi : Independent C)
    (u : Vertex) (hu : C u = false) :
    ∃ x y : Vertex, C x = true ∧ C y = true ∧ adjacent u x = true ∧
      adjacent u y = true ∧ x ≠ y := by
  obtain ⟨x, hx, hux⟩ := hc.1 u
  have hne : u ≠ x := by intro hh; subst x; simp_all
  have hux' := cube_adjacent_of_closed hux hne
  obtain ⟨y, hy, hd⟩ := ((localIdentifying_iff_constraints C).mp hc).2 u x hux'
  have hyx : y ≠ x := by intro hh; subst y; exact hd (hux.trans (cube_closed_self x).symm)
  have hxy : closed x y = false := by simp [closed, Ne.symm hyx, hi x y hx hy]
  have huy : closed u y = true := by cases hh : closed u y <;> simp_all
  have huney : u ≠ y := by intro hh; subst y; simp_all
  exact ⟨x, y, hx, hy, hux', cube_adjacent_of_closed huy huney, Ne.symm hyx⟩


namespace PathCounting

theorem count_two {α : Type} (l : List α) (p : α → Bool) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (hpx : p x = true) (hpy : p y = true) (hne : x ≠ y) :
    2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hx' : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
  have hy' : y ∈ l.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
  generalize l.filter p = L at *
  cases L with
  | nil => simp at hx'
  | cons z zs =>
    cases zs with
    | nil => simp only [List.mem_singleton] at hx' hy'; exact False.elim (hne (hx'.trans hy'.symm))
    | cons w ws => simp

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_const {α : Type} (l : List α) (k : Nat) :
    (l.map (fun _ => k)).sum = k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_congr {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x = g x) : (l.map f).sum = (l.map g).sum := by
  apply congrArg List.sum
  exact List.map_congr_left h

theorem sum_swap {α β : Type} (l : List α) (m : List β) (f : α → β → Nat) :
    (l.map (fun x => (m.map (f x)).sum)).sum =
      (m.map (fun y => (l.map (fun x => f x y)).sum)).sum := by
  induction l with
  | nil => simp [sum_map_const]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_add, ih]

theorem sum_indicator {α : Type} (l : List α) (p : α → Bool) (k : Nat) :
    (l.map (fun x => if p x then k else 0)).sum = k * l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases p a <;> simp [Nat.mul_add, Nat.add_comm]

end PathCounting

def codeDegree (C : Code) (u : Vertex) : Nat :=
  vertices.countP (fun x => C x && adjacent u x)

theorem outside_degree_two (C : Code) (hc : LocalIdentifying C) (hi : Independent C)
    (u : Vertex) (hu : C u = false) : 2 ≤ codeDegree C u := by
  obtain ⟨x, y, hx, hy, hux, huy, hne⟩ := independent_outside_two C hc hi u hu
  exact PathCounting.count_two vertices _ x y (translation_vertices_complete x)
    (translation_vertices_complete y) (by simp [hx, hux]) (by simp [hy, huy]) hne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cube_degree_six : ∀ x : Vertex, vertices.countP (fun u => adjacent u x) = 6 := by
  decide +kernel

theorem sum_codeDegree (C : Code) : (vertices.map (codeDegree C)).sum = 6 * cardinality C := by
  have he : ∀ u, codeDegree C u =
      (vertices.map (fun x => if C x && adjacent u x then 1 else 0)).sum := by
    intro u
    rw [PathCounting.sum_indicator]
    simp [codeDegree]
  have h := PathCounting.sum_map_congr vertices (codeDegree C)
    (fun u => (vertices.map (fun x => if C x && adjacent u x then 1 else 0)).sum)
    (fun u _ => he u)
  rw [h, PathCounting.sum_swap]
  have hf : ∀ x, (vertices.map (fun u => if C x && adjacent u x then 1 else 0)).sum =
      if C x then 6 else 0 := by
    intro x
    cases hh : C x
    · simp [PathCounting.sum_map_const]
    · simp only [Bool.true_and]
      rw [PathCounting.sum_indicator, cube_degree_six]
      simp
  rw [PathCounting.sum_map_congr vertices _ _ (fun x _ => hf x), PathCounting.sum_indicator]
  simp only [List.countP_eq_length_filter, cardinality]

theorem independent_cardinality_sixteen (C : Code) (hc : LocalIdentifying C) (hi : Independent C) :
    16 ≤ cardinality C := by
  have hlocal : ∀ u : Vertex, 2 ≤ codeDegree C u + if C u then 2 else 0 := by
    intro u
    cases hh : C u
    · simpa using outside_degree_two C hc hi u hh
    · simp
  have hsum := PathCounting.sum_map_le vertices (fun _ => 2)
    (fun u => codeDegree C u + if C u then 2 else 0) (fun u _ => hlocal u)
  rw [PathCounting.sum_map_const, PathCounting.sum_map_add, sum_codeDegree,
    PathCounting.sum_indicator] at hsum
  have hn : vertices.length = 64 := by decide
  simp only [hn, List.countP_eq_length_filter] at hsum
  change 2 * 64 ≤ 6 * cardinality C + 2 * cardinality C at hsum
  omega

theorem small_code_has_path (C : Code) (hc : LocalIdentifying C) (hcard : cardinality C ≤ 13) :
    CodePath C := by
  classical
  apply Classical.byContradiction
  intro hn
  have hh := independent_cardinality_sixteen C hc (no_path_independent C hc hn)
  omega

#print axioms small_code_has_path
end LocalIdentifyingQ6
