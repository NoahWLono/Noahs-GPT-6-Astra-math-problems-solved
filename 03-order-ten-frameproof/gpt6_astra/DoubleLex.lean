import CryptographyResearch
import Mathlib.Order.PiLex
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace GPT6Astra

abbrev LexRow10 := Lex (Fin 10 → Bool)

noncomputable def matrixLexKey (A : BinaryMatrix 10) : Lex (Fin 10 → LexRow10) :=
  toLex (fun r => toLex (A r))

noncomputable def columnLexKey (A : BinaryMatrix 10) (c : Fin 10) : LexRow10 :=
  toLex (fun r => A r c)

/-- Prefix formulation of the usual false-before-true lexicographic order. -/
def PrefixLexLE (x y : Fin 10 → Bool) : Prop :=
  ∀ c, (∀ d, d < c → x d = y d) → x c ≤ y c

theorem prefixLexLE_of_lex_le {x y : Fin 10 → Bool}
    (h : toLex x ≤ toLex y) : PrefixLexLE x y := by
  intro c heq
  by_contra! hlt
  have hyx : toLex y < toLex x := by
    exact ⟨c, fun d hd => (heq d hd).symm, hlt⟩
  exact (not_lt_of_ge h) hyx

theorem rowSwap_key_lt (A : BinaryMatrix 10) (i j : Fin 10) (hij : i < j)
    (hlt : toLex (A j) < toLex (A i)) :
    matrixLexKey (fun r c => A (Equiv.swap i j r) c) < matrixLexKey A := by
  refine ⟨i, ?_, ?_⟩
  · intro r hr
    have hri : r ≠ i := ne_of_lt hr
    have hrj : r ≠ j := ne_of_lt (hr.trans hij)
    simp [matrixLexKey, Equiv.swap_apply_of_ne_of_ne hri hrj]
  · simpa [matrixLexKey] using hlt

theorem columnSwap_key_lt (A : BinaryMatrix 10) (i j : Fin 10) (hij : i < j)
    (hlt : columnLexKey A j < columnLexKey A i) :
    matrixLexKey (fun r c => A r (Equiv.swap i j c)) < matrixLexKey A := by
  obtain ⟨r, heq, hbit⟩ := hlt
  refine ⟨r, ?_, ?_⟩
  · intro s hs
    apply congrArg toLex
    funext c
    by_cases hci : c = i
    · subst c
      simpa [columnLexKey] using heq s hs
    by_cases hcj : c = j
    · subst c
      simpa [columnLexKey] using (heq s hs).symm
    simp [Equiv.swap_apply_of_ne_of_ne hci hcj]
  · refine ⟨i, ?_, ?_⟩
    · intro c hc
      have hci : c ≠ i := ne_of_lt hc
      have hcj : c ≠ j := ne_of_lt (hc.trans hij)
      simp [matrixLexKey, Equiv.swap_apply_of_ne_of_ne hci hcj]
    · simpa [matrixLexKey, columnLexKey] using hbit

/-- Simultaneously sorting the free rows and each fixed-first-row column block
is justified by minimization over the finite permutation orbit. -/
theorem exists_doubleLex (A : BinaryMatrix 10) (k : Nat) :
    ∃ (q p : Equiv.Perm (Fin 10)), q 0 = 0 ∧
      (∀ c, (p c).val < k ↔ c.val < k) ∧
      (∀ i j : Fin 10, 0 < i → i < j →
        PrefixLexLE (fun c => A (q i) (p c)) (fun c => A (q j) (p c))) ∧
      (∀ c d : Fin 10, c < d → (c.val < k ↔ d.val < k) →
        PrefixLexLE (fun r => A (q r) (p c)) (fun r => A (q r) (p d))) := by
  classical
  let OrbitPerm := {qp : Equiv.Perm (Fin 10) × Equiv.Perm (Fin 10) //
    qp.1 0 = 0 ∧ ∀ c, (qp.2 c).val < k ↔ c.val < k}
  let : Nonempty OrbitPerm := ⟨⟨(Equiv.refl _, Equiv.refl _), by simp⟩⟩
  let key (z : OrbitPerm) := matrixLexKey (fun r c => A (z.val.1 r) (z.val.2 c))
  obtain ⟨z, hmin⟩ := Finite.exists_min key
  let q := z.val.1
  let p := z.val.2
  let B : BinaryMatrix 10 := fun r c => A (q r) (p c)
  have hq : q 0 = 0 := z.property.1
  have hp : ∀ c, (p c).val < k ↔ c.val < k := z.property.2
  refine ⟨q, p, hq, hp, ?_, ?_⟩
  · intro i j hi hij
    apply prefixLexLE_of_lex_le
    by_contra! hlt
    let q' := (Equiv.swap i j).trans q
    have hq' : q' 0 = 0 := by
      have h0i : (0 : Fin 10) ≠ i := ne_of_lt hi
      have h0j : (0 : Fin 10) ≠ j := ne_of_lt (hi.trans hij)
      simp [q', Equiv.swap_apply_of_ne_of_ne h0i h0j, hq]
    let z' : OrbitPerm := ⟨(q', p), hq', hp⟩
    have hsmall : key z' < key z := by
      simpa [key, z', q', B, q, p] using rowSwap_key_lt B i j hij hlt
    exact (not_lt_of_ge (hmin z')) hsmall
  · intro c d hcd hpart
    apply prefixLexLE_of_lex_le
    by_contra! hlt
    let p' := (Equiv.swap c d).trans p
    have hp' : ∀ x, (p' x).val < k ↔ x.val < k := by
      intro x
      change (p (Equiv.swap c d x)).val < k ↔ x.val < k
      rw [hp]
      by_cases hxc : x = c
      · subst x
        simpa using hpart.symm
      by_cases hxd : x = d
      · subst x
        simpa using hpart
      simp [Equiv.swap_apply_of_ne_of_ne hxc hxd]
    let z' : OrbitPerm := ⟨(q, p'), hq, hp'⟩
    have hsmall : key z' < key z := by
      simpa [key, z', p', B, q, p, columnLexKey] using columnSwap_key_lt B c d hcd hlt
    exact (not_lt_of_ge (hmin z')) hsmall

def DoubleLexRows (A : BinaryMatrix 10) : Prop :=
  ∀ i j : Fin 10, 0 < i → i < j → PrefixLexLE (A i) (A j)

/-- The first row is omitted because it is constant inside each column block. -/
def DoubleLexColumns (A : BinaryMatrix 10) (k : Nat) : Prop :=
  ∀ c d : Fin 10, c < d → (c.val < k ↔ d.val < k) →
    ∀ r : Fin 10, 0 < r →
      (∀ s : Fin 10, 0 < s → s < r → A s c = A s d) → A r c ≤ A r d

theorem exists_doubleLex_fixed (A : BinaryMatrix 10) (k : Nat)
    (hfirst : ∀ c : Fin 10, A 0 c = decide (c.val < k)) :
    ∃ (q p : Equiv.Perm (Fin 10)), q 0 = 0 ∧
      (∀ c, (p c).val < k ↔ c.val < k) ∧
      DoubleLexRows (fun r c => A (q r) (p c)) ∧
      DoubleLexColumns (fun r c => A (q r) (p c)) k := by
  classical
  obtain ⟨q, p, hq, hp, hrows, hcols⟩ := exists_doubleLex A k
  refine ⟨q, p, hq, hp, hrows, ?_⟩
  intro c d hcd hpart r hr hprefix
  apply hcols c d hcd hpart r
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    dsimp only
    rw [hq, hfirst, hfirst]
    exact Bool.decide_congr ((hp c).trans (hpart.trans (hp d).symm))
  · exact hprefix s (Fin.pos_iff_ne_zero.mpr hs0) hs

theorem exists_doubleLex_anchored (A : BinaryMatrix 10) (k : Nat) :
    ∃ (q p : Equiv.Perm (Fin 10)), q 0 = 0 ∧ p 0 = 0 ∧
      (∀ c, (p c).val < k ↔ c.val < k) ∧
      (∀ i j : Fin 10, 0 < i → i < j →
        PrefixLexLE (fun c => A (q i) (p c)) (fun c => A (q j) (p c))) ∧
      (∀ c d : Fin 10, 0 < c → c < d → (c.val < k ↔ d.val < k) →
        PrefixLexLE (fun r => A (q r) (p c)) (fun r => A (q r) (p d))) := by
  classical
  let OrbitPerm := {qp : Equiv.Perm (Fin 10) × Equiv.Perm (Fin 10) //
    qp.1 0 = 0 ∧ qp.2 0 = 0 ∧ ∀ c, (qp.2 c).val < k ↔ c.val < k}
  let : Nonempty OrbitPerm := ⟨⟨(Equiv.refl _, Equiv.refl _), by simp⟩⟩
  let key (z : OrbitPerm) := matrixLexKey (fun r c => A (z.val.1 r) (z.val.2 c))
  obtain ⟨z, hmin⟩ := Finite.exists_min key
  let q := z.val.1
  let p := z.val.2
  let B : BinaryMatrix 10 := fun r c => A (q r) (p c)
  have hq : q 0 = 0 := z.property.1
  have hp0 : p 0 = 0 := z.property.2.1
  have hp : ∀ c, (p c).val < k ↔ c.val < k := z.property.2.2
  refine ⟨q, p, hq, hp0, hp, ?_, ?_⟩
  · intro i j hi hij
    apply prefixLexLE_of_lex_le
    by_contra! hlt
    let q' := (Equiv.swap i j).trans q
    have hq' : q' 0 = 0 := by
      have h0i : (0 : Fin 10) ≠ i := ne_of_lt hi
      have h0j : (0 : Fin 10) ≠ j := ne_of_lt (hi.trans hij)
      simp [q', Equiv.swap_apply_of_ne_of_ne h0i h0j, hq]
    let z' : OrbitPerm := ⟨(q', p), hq', hp0, hp⟩
    have hsmall : key z' < key z := by
      simpa [key, z', q', B, q, p] using rowSwap_key_lt B i j hij hlt
    exact (not_lt_of_ge (hmin z')) hsmall
  · intro c d hc hcd hpart
    apply prefixLexLE_of_lex_le
    by_contra! hlt
    let p' := (Equiv.swap c d).trans p
    have hp0' : p' 0 = 0 := by
      have h0c : (0 : Fin 10) ≠ c := ne_of_lt hc
      have h0d : (0 : Fin 10) ≠ d := ne_of_lt (hc.trans hcd)
      simp [p', Equiv.swap_apply_of_ne_of_ne h0c h0d, hp0]
    have hp' : ∀ x, (p' x).val < k ↔ x.val < k := by
      intro x
      change (p (Equiv.swap c d x)).val < k ↔ x.val < k
      rw [hp]
      by_cases hxc : x = c
      · subst x
        simpa using hpart.symm
      by_cases hxd : x = d
      · subst x
        simpa using hpart
      simp [Equiv.swap_apply_of_ne_of_ne hxc hxd]
    let z' : OrbitPerm := ⟨(q, p'), hq, hp0', hp'⟩
    have hsmall : key z' < key z := by
      simpa [key, z', p', B, q, p, columnLexKey] using columnSwap_key_lt B c d hcd hlt
    exact (not_lt_of_ge (hmin z')) hsmall

/-- Residual column sorting when column zero is held fixed. -/
def DoubleLexAnchoredColumns (A : BinaryMatrix 10) (k : Nat) : Prop :=
  ∀ c d : Fin 10, 0 < c → c < d → (c.val < k ↔ d.val < k) →
    ∀ r : Fin 10, 0 < r →
      (∀ s : Fin 10, 0 < s → s < r → A s c = A s d) → A r c ≤ A r d

theorem exists_doubleLex_anchored_fixed (A : BinaryMatrix 10) (k : Nat)
    (hfirst : ∀ c : Fin 10, A 0 c = decide (c.val < k)) :
    ∃ (q p : Equiv.Perm (Fin 10)), q 0 = 0 ∧ p 0 = 0 ∧
      (∀ c, (p c).val < k ↔ c.val < k) ∧
      DoubleLexRows (fun r c => A (q r) (p c)) ∧
      DoubleLexAnchoredColumns (fun r c => A (q r) (p c)) k := by
  classical
  obtain ⟨q, p, hq, hp0, hp, hrows, hcols⟩ := exists_doubleLex_anchored A k
  refine ⟨q, p, hq, hp0, hp, hrows, ?_⟩
  intro c d hc hcd hpart r hr hprefix
  apply hcols c d hc hcd hpart r
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    dsimp only
    rw [hq, hfirst, hfirst]
    exact Bool.decide_congr ((hp c).trans (hpart.trans (hp d).symm))
  · exact hprefix s (Fin.pos_iff_ne_zero.mpr hs0) hs

#print axioms exists_doubleLex_anchored
#print axioms exists_doubleLex_anchored_fixed

#print axioms exists_doubleLex
#print axioms exists_doubleLex_fixed

end GPT6Astra
