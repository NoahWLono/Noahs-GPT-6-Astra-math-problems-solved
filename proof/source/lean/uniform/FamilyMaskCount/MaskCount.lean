import FamilyAlgebra.ParameterData
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases

namespace FamilyMaskCount
abbrev F := ZMod 2
abbrev Bits (n : Nat) := Fin n → F

def splitAt (a b : Nat) : Bits (a+b) ≃ Bits a × Bits b :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) F)

@[simp] theorem splitAt_left (a b : Nat) (v : Bits (a+b)) (i : Fin a) :
    (splitAt a b v).1 i = v ⟨i.val, by omega⟩ := rfl
@[simp] theorem splitAt_right (a b : Nat) (v : Bits (a+b)) (i : Fin b) :
    (splitAt a b v).2 i = v ⟨a+i.val, by omega⟩ := rfl

def castBits {a b : Nat} (h : a=b) : Bits a ≃ Bits b :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl F)

@[simp] theorem castBits_apply {a b : Nat} (h : a=b) (v : Bits a) (i : Fin b) :
    castBits h v i = v ⟨i.val, by omega⟩ := rfl

/-- Canonical consecutive blocks: base, extension, and padding, all little-endian. -/
def split (e : Nat) (he : 0<e) :
    Bits (4*e) ≃ Bits 4 × (Bits (2*(e-1)) × Bits (2*e-2)) :=
  (castBits (show 4*e=4+(2*(e-1)+(2*e-2)) by omega)).trans
    ((splitAt 4 (2*(e-1)+(2*e-2))).trans
      (Equiv.prodCongr (Equiv.refl _) (splitAt (2*(e-1)) (2*e-2))))

@[simp] theorem split_base (e : Nat) (he : 0<e) (v : Bits (4*e)) (i : Fin 4) :
    (split e he v).1 i = v ⟨i.val, by omega⟩ := rfl
@[simp] theorem split_extension (e : Nat) (he : 0<e) (v : Bits (4*e)) (i : Fin (2*(e-1))) :
    (split e he v).2.1 i = v ⟨4+i.val, by omega⟩ := rfl
@[simp] theorem split_padding (e : Nat) (he : 0<e) (v : Bits (4*e)) (i : Fin (2*e-2)) :
    (split e he v).2.2 i = v ⟨2*e+2+i.val, by omega⟩ := by
  change v ⟨4+(2*(e-1)+i.val), _⟩ = _
  congr 1
  apply Fin.ext
  dsimp
  omega

def bit (z : F) : Bool := decide (z≠0)
def baseBad (b : Bits 4) : Prop :=
  (bit (b 0),bit (b 1),bit (b 2),bit (b 3)) ∈ FamilyAlgebra.sixBaseTuples
instance (b : Bits 4) : Decidable (baseBad b) := inferInstanceAs (Decidable (_ ∈ _))

/-- Literal little-endian integer encoding of the four base coordinates. -/
def baseCode (b : Bits 4) : Nat :=
  (b 0).val + 2*(b 1).val + 4*(b 2).val + 8*(b 3).val

theorem baseBad_codes (b : Bits 4) :
    baseBad b ↔ baseCode b ∈ [0,4,8,13,14,15] := by
  revert b
  decide

/-- Six base masks, including the zero mask. -/
theorem baseBad_card : Fintype.card {b : Bits 4 // baseBad b}=6 := by decide

theorem baseBad_zero : baseBad 0 := by decide

def Bad (e : Nat) (he : 0<e) (v : Bits (4*e)) : Prop :=
  baseBad (split e he v).1 ∧ (split e he v).2.1=0
instance (e : Nat) (he : 0<e) (v : Bits (4*e)) : Decidable (Bad e he v) :=
  inferInstanceAs (Decidable (_ ∧ _))

def badEquiv (e : Nat) (he : 0<e) :
    {v : Bits (4*e) // Bad e he v} ≃ {b : Bits 4 // baseBad b} × Bits (2*e-2) where
  toFun v := (⟨(split e he v.val).1,v.property.1⟩, (split e he v.val).2.2)
  invFun p := ⟨(split e he).symm (p.1.val,0,p.2), by
    change baseBad ((split e he) ((split e he).symm _)).1 ∧ _
    simp only [Equiv.apply_symm_apply]
    exact ⟨p.1.property, trivial⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply (split e he).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext rfl (Prod.ext v.property.2.symm rfl)
  right_inv p := by
    simp only [Equiv.apply_symm_apply]

theorem bad_card (e : Nat) (he : 0<e) :
    Fintype.card {v : Bits (4*e) // Bad e he v} = 6*2^(2*e-2) := by
  rw [Fintype.card_congr (badEquiv e he), Fintype.card_prod, baseBad_card]
  simp [Bits, F]

theorem bad_zero (e : Nat) (he : 0<e) : Bad e he 0 := by
  constructor
  · change baseBad (fun _ => 0)
    exact baseBad_zero
  · rfl

theorem nonzero_bad_card_add_one (e : Nat) (he : 0<e) :
    Fintype.card {v : Bits (4*e) // Bad e he v ∧ v≠0} + 1 = 6*2^(2*e-2) := by
  have hz : (0 : Bits (4*e)) ∈ Finset.univ.filter (Bad e he) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact bad_zero e he
  have herase : (Finset.univ.filter (Bad e he)).erase 0 =
      Finset.univ.filter (fun v => Bad e he v ∧ v≠0) := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have h := Finset.card_erase_add_one hz
  rw [herase] at h
  rw [Fintype.card_subtype]
  rw [h]
  rw [← Fintype.card_subtype, bad_card]

theorem nonzero_bad_card (e : Nat) (he : 0<e) :
    Fintype.card {v : Bits (4*e) // Bad e he v ∧ v≠0} = 3*2^(2*e-1)-1 := by
  have h := nonzero_bad_card_add_one e he
  have hexp : 2*e-1=(2*e-2)+1 := by omega
  rw [hexp, pow_succ]
  have hmul : 3*(2^(2*e-2)*2) = 6*2^(2*e-2) := by omega
  rw [hmul]
  omega

theorem bad_card_e_one : Fintype.card {v : Bits 4 // Bad 1 (by decide) v}=6 := by
  simpa using bad_card 1 (by decide)
theorem nonzero_bad_card_e_one :
    Fintype.card {v : Bits 4 // Bad 1 (by decide) v ∧ v≠0}=5 := by
  simpa using nonzero_bad_card 1 (by decide)

theorem bad_iff_badFullMask (e : Nat) (he : 0<e) (v : Bits (4*e)) :
    Bad e he v ↔ FamilyAlgebra.badFullMask e he v := by
  have h0 : 0<2*e+2 := by omega
  have h1 : 1<2*e+2 := by omega
  have h2 : 2<2*e+2 := by omega
  have h3 : 3<2*e+2 := by omega
  unfold Bad FamilyAlgebra.badFullMask FamilyAlgebra.badParameters
  simp only [baseBad, split_base, FamilyAlgebra.paramRead, h0, h1, h2, h3,
    dite_true, FamilyAlgebra.projectParameters]
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr Iff.rfl
  constructor
  · intro hz k hk
    have hi : k.val-4<2*(e-1) := by have := k.isLt; omega
    have hh := congrFun hz ⟨k.val-4,hi⟩
    rw [split_extension] at hh
    change v ⟨4+(k.val-4),_⟩=0 at hh
    convert hh using 1 <;> congr 1 <;> apply Fin.ext <;> dsimp <;> omega
  · intro hz
    funext i
    rw [split_extension]
    exact hz ⟨4+i.val, by have := i.isLt; omega⟩ (by dsimp; omega)

instance (e : Nat) (he : 0<e) (v : Bits (4*e)) :
    Decidable (FamilyAlgebra.badFullMask e he v) :=
  decidable_of_iff (Bad e he v) (bad_iff_badFullMask e he v)

theorem badFullMask_card (e : Nat) (he : 0<e) :
    Fintype.card {v : Bits (4*e) // FamilyAlgebra.badFullMask e he v} =
      6*2^(2*e-2) := by
  simp_rw [← bad_iff_badFullMask]
  exact bad_card e he

theorem nonzero_badFullMask_card_add_one (e : Nat) (he : 0<e) :
    Fintype.card {v : Bits (4*e) // FamilyAlgebra.badFullMask e he v ∧ v≠0}+1 =
      6*2^(2*e-2) := by
  simp_rw [← bad_iff_badFullMask]
  exact nonzero_bad_card_add_one e he

theorem nonzero_badFullMask_card (e : Nat) (he : 0<e) :
    Fintype.card {v : Bits (4*e) // FamilyAlgebra.badFullMask e he v ∧ v≠0} =
      3*2^(2*e-1)-1 := by
  simp_rw [← bad_iff_badFullMask]
  exact nonzero_bad_card e he

#print axioms bad_card
#print axioms nonzero_bad_card
end FamilyMaskCount
