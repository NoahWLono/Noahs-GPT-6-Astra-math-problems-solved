import LocalIdentifyingQ6
namespace LocalIdentifyingQ6

def translate (a x : Vertex) : Vertex :=
  ⟨a.val ^^^ x.val, Nat.xor_lt_two_pow (n := 6) a.isLt x.isLt⟩

theorem translate_involutive (a x : Vertex) : translate a (translate a x) = x := by
  apply Fin.ext
  simp [translate, ← Nat.xor_assoc]

theorem translate_zero (a : Vertex) : translate a 0 = a := by
  apply Fin.ext
  simp [translate]

theorem translate_injective (a x y : Vertex) : translate a x = translate a y ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (translate a) h
    simpa only [translate_involutive] using hh
  · intro h; exact congrArg _ h

theorem translate_xor (a u v : Vertex) :
    (translate a u).val ^^^ (translate a v).val = u.val ^^^ v.val := by
  simp only [translate]
  calc
    (a.val ^^^ u.val) ^^^ (a.val ^^^ v.val) =
        u.val ^^^ (a.val ^^^ a.val) ^^^ v.val := by
      rw [Nat.xor_comm a.val u.val, ← Nat.xor_assoc, Nat.xor_assoc u.val a.val a.val]
    _ = _ := by simp

theorem translate_adjacent (a u v : Vertex) :
    adjacent (translate a u) (translate a v) = adjacent u v := by
  unfold adjacent
  change [1, 2, 4, 8, 16, 32].contains ((translate a u).val ^^^ (translate a v).val) = _
  rw [translate_xor]
  rfl

theorem translate_closed (a u v : Vertex) :
    closed (translate a u) (translate a v) = closed u v := by
  unfold closed
  rw [translate_adjacent]
  have he : (translate a u == translate a v) = (u == v) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, translate_injective]
  rw [he]

def translatedCode (a : Vertex) (C : Code) : Code := fun x => C (translate a x)

theorem translated_constraints (a : Vertex) (C : Code) (h : Constraints C) :
    Constraints (translatedCode a C) := by
  constructor
  · intro u
    obtain ⟨x, hx, hn⟩ := h.1 (translate a u)
    refine ⟨translate a x, ?_, ?_⟩
    · simpa only [translatedCode, translate_involutive] using hx
    · have hh := translate_closed a (translate a u) x
      simpa only [translate_involutive] using hh.trans hn
  · intro u v huv
    have hadj : adjacent (translate a u) (translate a v) = true :=
      (translate_adjacent a u v).trans huv
    obtain ⟨x, hx, hd⟩ := h.2 (translate a u) (translate a v) hadj
    refine ⟨translate a x, ?_, ?_⟩
    · simpa only [translatedCode, translate_involutive] using hx
    · have hu := translate_closed a (translate a u) x
      have hv := translate_closed a (translate a v) x
      simp only [translate_involutive] at hu hv
      simpa only [hu, hv] using hd

theorem vertices_nodup : vertices.Nodup := by decide

theorem translation_vertices_complete (v : Vertex) : v ∈ vertices := by
  change v ∈ List.ofFn (fun x : Fin 64 => x)
  exact List.mem_ofFn.mpr ⟨v, rfl⟩

theorem translated_vertices_permutation (a : Vertex) :
    (vertices.map (translate a)).Perm vertices := by
  apply List.perm_iff_count.mpr
  intro x
  have hn : (vertices.map (translate a)).Nodup := by
    exact List.Pairwise.map (translate a) (fun u v h huv => h ((translate_injective a u v).mp huv)) vertices_nodup
  rw [hn.count, vertices_nodup.count]
  have hx : x ∈ vertices.map (translate a) :=
    List.mem_map.mpr ⟨translate a x, translation_vertices_complete _, translate_involutive a x⟩
  simp only [hx, translation_vertices_complete, if_true]

theorem translated_cardinality (a : Vertex) (C : Code) :
    cardinality (translatedCode a C) = cardinality C := by
  have h := ((translated_vertices_permutation a).filter C).length_eq
  simpa only [List.filter_map, List.length_map, cardinality, translatedCode,
    Function.comp_def] using h

theorem normalize_zero (C : Code) (h : LocalIdentifying C) :
    ∃ D : Code, LocalIdentifying D ∧ D 0 = true ∧ cardinality D = cardinality C := by
  obtain ⟨a, ha, _⟩ := h.1 0
  refine ⟨translatedCode a C, ?_, ?_, translated_cardinality a C⟩
  · apply (localIdentifying_iff_constraints _).mpr
    exact translated_constraints a C ((localIdentifying_iff_constraints _).mp h)
  · simpa only [translatedCode, translate_zero] using ha

#print axioms normalize_zero
end LocalIdentifyingQ6
