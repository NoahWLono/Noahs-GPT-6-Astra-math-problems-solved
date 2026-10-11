import Translation
namespace LocalIdentifyingQ6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def coordinateWeight (i : Fin 6) : Vertex :=
  ⟨2 ^ i.val, by
    have h : ∀ i : Fin 6, 2 ^ i.val < 64 := by decide +kernel
    exact h i⟩

def swapCoordinates (j : Fin 2) (i : Fin 6) (x : Vertex) : Vertex :=
  if x.val.testBit j.val == x.val.testBit i.val then x
  else translate (translate (coordinateWeight ⟨j.val, by omega⟩) (coordinateWeight i)) x

theorem swapCoordinates_involutive : ∀ j i x,
    swapCoordinates j i (swapCoordinates j i x) = x := by decide +kernel

theorem swap_adj_0_0 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 0 0 u) (swapCoordinates 0 0 v) = true := by decide +kernel

theorem swap_adj_0_1 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 0 1 u) (swapCoordinates 0 1 v) = true := by decide +kernel

theorem swap_adj_0_2 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 0 2 u) (swapCoordinates 0 2 v) = true := by decide +kernel

theorem swap_adj_0_3 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 0 3 u) (swapCoordinates 0 3 v) = true := by decide +kernel

theorem swap_adj_0_4 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 0 4 u) (swapCoordinates 0 4 v) = true := by decide +kernel

theorem swap_adj_0_5 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 0 5 u) (swapCoordinates 0 5 v) = true := by decide +kernel

theorem swap_adj_1_0 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 1 0 u) (swapCoordinates 1 0 v) = true := by decide +kernel

theorem swap_adj_1_1 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 1 1 u) (swapCoordinates 1 1 v) = true := by decide +kernel

theorem swap_adj_1_2 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 1 2 u) (swapCoordinates 1 2 v) = true := by decide +kernel

theorem swap_adj_1_3 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 1 3 u) (swapCoordinates 1 3 v) = true := by decide +kernel

theorem swap_adj_1_4 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 1 4 u) (swapCoordinates 1 4 v) = true := by decide +kernel

theorem swap_adj_1_5 : ∀ u v : Vertex, adjacent u v = true →
    adjacent (swapCoordinates 1 5 u) (swapCoordinates 1 5 v) = true := by decide +kernel

theorem swapCoordinates_adjacent_forward : ∀ j i u v,
    adjacent u v = true → adjacent (swapCoordinates j i u) (swapCoordinates j i v) = true := by
  intro j i
  have hj : j = 0 ∨ j = 1 := by omega
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact swap_adj_0_0
  · exact swap_adj_0_1
  · exact swap_adj_0_2
  · exact swap_adj_0_3
  · exact swap_adj_0_4
  · exact swap_adj_0_5
  · exact swap_adj_1_0
  · exact swap_adj_1_1
  · exact swap_adj_1_2
  · exact swap_adj_1_3
  · exact swap_adj_1_4
  · exact swap_adj_1_5

theorem swapCoordinates_adjacent (j : Fin 2) (i : Fin 6) (u v : Vertex) :
    adjacent (swapCoordinates j i u) (swapCoordinates j i v) = adjacent u v := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hh := swapCoordinates_adjacent_forward j i _ _ h
    simpa only [swapCoordinates_involutive] using hh
  · exact swapCoordinates_adjacent_forward j i u v


def relabeledCode (f : Vertex → Vertex) (C : Code) : Code := fun x => C (f x)

theorem relabel_closed (f : Vertex → Vertex)
    (hi : ∀ x, f (f x) = x)
    (ha : ∀ u v, adjacent (f u) (f v) = adjacent u v) (u v : Vertex) :
    closed (f u) (f v) = closed u v := by
  have hinj : ∀ u v, f u = f v ↔ u = v := by
    intro u v; constructor
    · intro h; have hh := congrArg f h; simpa only [hi] using hh
    · exact congrArg f
  unfold closed
  rw [ha]
  have he : (f u == f v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, hinj]
  rw [he]

theorem relabel_constraints (f : Vertex → Vertex)
    (hi : ∀ x, f (f x) = x)
    (ha : ∀ u v, adjacent (f u) (f v) = adjacent u v)
    (C : Code) (h : Constraints C) : Constraints (relabeledCode f C) := by
  constructor
  · intro u
    obtain ⟨x, hx, hn⟩ := h.1 (f u)
    refine ⟨f x, ?_, ?_⟩
    · simpa only [relabeledCode, hi] using hx
    · have hh := relabel_closed f hi ha (f u) x
      simpa only [hi] using hh.trans hn
  · intro u v huv
    have hadj : adjacent (f u) (f v) = true := (ha u v).trans huv
    obtain ⟨x, hx, hd⟩ := h.2 (f u) (f v) hadj
    refine ⟨f x, ?_, ?_⟩
    · simpa only [relabeledCode, hi] using hx
    · have hu := relabel_closed f hi ha (f u) x
      have hv := relabel_closed f hi ha (f v) x
      simp only [hi] at hu hv
      simpa only [hu, hv] using hd

theorem relabel_cardinality (f : Vertex → Vertex)
    (hi : ∀ x, f (f x) = x) (C : Code) :
    cardinality (relabeledCode f C) = cardinality C := by
  have hinj : ∀ u v, f u = f v → u = v := by
    intro u v h; have hh := congrArg f h; simpa only [hi] using hh
  have hp : (vertices.map f).Perm vertices := by
    apply List.perm_iff_count.mpr
    intro x
    have hn : (vertices.map f).Nodup :=
      List.Pairwise.map f (fun u v h huv => h (hinj u v huv)) vertices_nodup
    rw [hn.count, vertices_nodup.count]
    have hx : x ∈ vertices.map f :=
      List.mem_map.mpr ⟨f x, translation_vertices_complete _, hi x⟩
    simp only [hx, translation_vertices_complete, if_true]
  have h := (hp.filter C).length_eq
  simpa only [List.filter_map, List.length_map, cardinality, relabeledCode,
    Function.comp_def] using h

theorem neighbor_pair_coordinates : ∀ p q : Vertex,
    adjacent 0 p = true → adjacent 0 q = true → p ≠ q →
    ∃ i j : Fin 6,
      swapCoordinates 0 i (swapCoordinates 1 j 0) = 0 ∧
      swapCoordinates 0 i (swapCoordinates 1 j 1) = p ∧
      swapCoordinates 0 i (swapCoordinates 1 j 2) = q := by decide +kernel


theorem normalize_code_path (C : Code) (h : LocalIdentifying C)
    (c a b : Vertex) (hc : C c = true) (ha : C a = true) (hb : C b = true)
    (hca : adjacent c a = true) (hcb : adjacent c b = true) (hab : a ≠ b) :
    ∃ D : Code, LocalIdentifying D ∧ D 0 = true ∧ D 1 = true ∧ D 2 = true ∧
      cardinality D = cardinality C := by
  have hcc : translate c c = 0 := by apply Fin.ext; simp [translate]
  have hp : adjacent 0 (translate c a) = true := by
    simpa only [hcc] using (translate_adjacent c c a).trans hca
  have hq : adjacent 0 (translate c b) = true := by
    simpa only [hcc] using (translate_adjacent c c b).trans hcb
  have hpq : translate c a ≠ translate c b := by
    intro he; exact hab ((translate_injective c a b).mp he)
  obtain ⟨i, j, h0, h1, h2⟩ := neighbor_pair_coordinates _ _ hp hq hpq
  let C' := translatedCode c C
  let E := relabeledCode (swapCoordinates 0 i) C'
  let D := relabeledCode (swapCoordinates 1 j) E
  have hC' : Constraints C' := translated_constraints c C
    ((localIdentifying_iff_constraints C).mp h)
  have hE : Constraints E := relabel_constraints _ (swapCoordinates_involutive 0 i)
    (swapCoordinates_adjacent 0 i) C' hC'
  have hD : Constraints D := relabel_constraints _ (swapCoordinates_involutive 1 j)
    (swapCoordinates_adjacent 1 j) E hE
  refine ⟨D, (localIdentifying_iff_constraints D).mpr hD, ?_, ?_, ?_, ?_⟩
  · change C (translate c (swapCoordinates 0 i (swapCoordinates 1 j 0))) = true
    rw [h0, translate_zero]; exact hc
  · change C (translate c (swapCoordinates 0 i (swapCoordinates 1 j 1))) = true
    rw [h1, translate_involutive]; exact ha
  · change C (translate c (swapCoordinates 0 i (swapCoordinates 1 j 2))) = true
    rw [h2, translate_involutive]; exact hb
  · change cardinality (relabeledCode (swapCoordinates 1 j) E) = cardinality C
    rw [relabel_cardinality _ (swapCoordinates_involutive 1 j)]
    change cardinality (relabeledCode (swapCoordinates 0 i) C') = cardinality C
    rw [relabel_cardinality _ (swapCoordinates_involutive 0 i)]
    exact translated_cardinality c C

#print axioms normalize_code_path
end LocalIdentifyingQ6
