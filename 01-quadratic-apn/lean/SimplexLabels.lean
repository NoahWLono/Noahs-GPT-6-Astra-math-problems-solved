import CodeBasisProperties
import QuadraticFourSupport

set_option maxHeartbeats 200000

namespace BooleanANF
open scoped BigOperators

abbrev SimplexIndex := Fin 3 → F₂

def codeEvaluation {q : DoubleBlock → F₂}
    (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q) (y : Block) : SimplexIndex :=
  fun i => codeBasisWord e i y

theorem code_word_three_expansion {q : DoubleBlock → F₂}
    (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q) (u : SimplexIndex) :
    (e u).val = fun y => u 0 * codeBasisWord e 0 y +
      u 1 * codeBasisWord e 1 y + u 2 * codeBasisWord e 2 y := by
  funext y
  rw [code_word_expansion]
  simp [Fin.sum_univ_succ, add_assoc]

/-- Every nonzero evaluation column of the equality-case coefficient code occurs once. -/
theorem codeEvaluation_fiber_card {q : DoubleBlock → F₂}
    (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q)
    (hw : ∀ f ∈ quadraticCoefficientSpace q, f ≠ 0 → weight f = 4)
    (v : SimplexIndex) (hv : v ≠ 0) :
    (Finset.univ.filter (fun y : Block => codeEvaluation e y = v)).card = 1 := by
  let a := codeBasisWord e 0
  let b := codeBasisWord e 1
  let c := codeBasisWord e 2
  have hweight (u : SimplexIndex) (hu : u ≠ 0) : weight (e u).val = 4 :=
    hw _ (e u).property (code_word_ne_zero e hu)
  have h100 : weight a = 4 := hw _ (e (Pi.single 0 1)).property (codeBasisWord_ne_zero e 0)
  have h010 : weight b = 4 := hw _ (e (Pi.single 1 1)).property (codeBasisWord_ne_zero e 1)
  have h001 : weight c = 4 := hw _ (e (Pi.single 2 1)).property (codeBasisWord_ne_zero e 2)
  have h110 : weight (fun y => a y+b y) = 4 := by
    have hh := hweight (Pi.single 0 1 + Pi.single 1 1) (by
      intro hz; have hi := congrFun hz 0; simpa [Pi.single_apply] using hi)
    simpa [a,b,codeBasisWord,map_add] using hh
  have h101 : weight (fun y => a y+c y) = 4 := by
    have hh := hweight (Pi.single 0 1 + Pi.single 2 1) (by
      intro hz; have hi := congrFun hz 0; simpa [Pi.single_apply] using hi)
    simpa [a,c,codeBasisWord,map_add] using hh
  have h011 : weight (fun y => b y+c y) = 4 := by
    have hh := hweight (Pi.single 1 1 + Pi.single 2 1) (by
      intro hz; have hi := congrFun hz 1; simpa [Pi.single_apply] using hi)
    simpa [b,c,codeBasisWord,map_add] using hh
  have h111 : weight (fun y => a y+b y+c y) = 4 := by
    have hh := hweight (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1) (by
      intro hz; have hi := congrFun hz 0; simpa [Pi.single_apply] using hi)
    simpa [a,b,c,codeBasisWord,map_add] using hh
  have hp := simplex_pattern_counts a b c h100 h010 h001 h110 h101 h011 h111
  have he : (Finset.univ.filter (fun y : Block => codeEvaluation e y = v)).card =
      triplePatternCount a b c (v 0) (v 1) (v 2) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    have heq : codeEvaluation e y = v ↔
        a y = v 0 ∧ b y = v 1 ∧ c y = v 2 := by
      simp [funext_iff, Fin.forall_fin_succ, codeEvaluation, a,b,c]
    simp only [heq]
  rw [he]
  have h0 : v 0 = 0 ∨ v 0 = 1 := by generalize v 0 = t; fin_cases t <;> simp
  have h1 : v 1 = 0 ∨ v 1 = 1 := by generalize v 1 = t; fin_cases t <;> simp
  have h2 : v 2 = 0 ∨ v 2 = 1 := by generalize v 2 = t; fin_cases t <;> simp
  rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> rcases h2 with h2|h2
  · exfalso
    apply hv
    funext i
    fin_cases i <;> assumption
  · simpa only [h0,h1,h2] using hp.2.2.2.1
  · simpa only [h0,h1,h2] using hp.2.1
  · simpa only [h0,h1,h2] using hp.2.2.2.2.2.1
  · simpa only [h0,h1,h2] using hp.1
  · simpa only [h0,h1,h2] using hp.2.2.2.2.1
  · simpa only [h0,h1,h2] using hp.2.2.1
  · simpa only [h0,h1,h2] using hp.2.2.2.2.2.2

/-- Choose the seven simplex rows, retaining both inverse-evaluation and moment identities. -/
theorem exists_simplex_labels {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    ∃ (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q) (label : SimplexIndex → Block),
      (∀ v, v ≠ 0 → ∀ y, codeEvaluation e y = v ↔ y = label v) ∧
      (∀ i : Fin 3, ∑ v ∈ Finset.univ.filter (fun v : SimplexIndex => v i = 1), label v = 0) := by
  classical
  let e := codeEquiv (quadraticCoefficientSpace q) 3 hd
  have hw := (coefficientSpace_dimension_three h.totalDegree h.activeBound hd).2.2
  have hex (v : SimplexIndex) (hv : v ≠ 0) : ∃ a : Block,
      ∀ y, codeEvaluation e y = v ↔ y = a := by
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (codeEvaluation_fiber_card e hw v hv)
    refine ⟨a, ?_⟩
    intro y
    have hh := Finset.ext_iff.mp ha y
    simpa using hh
  let label : SimplexIndex → Block := fun v => if hv : v = 0 then 0 else Classical.choose (hex v hv)
  have hl (v : SimplexIndex) (hv : v ≠ 0) (y : Block) :
      codeEvaluation e y = v ↔ y = label v := by
    simp only [label, dif_neg hv]
    exact Classical.choose_spec (hex v hv) y
  refine ⟨e,label,hl,?_⟩
  intro i
  have hneq (v : SimplexIndex) (hv : v i = 1) : v ≠ 0 := by
    intro hz
    rw [hz] at hv
    exact zero_ne_one hv
  have hm := QuadraticFour.support_sum_zero (codeBasisWord_degree h.totalDegree e i)
  change (∑ y ∈ Finset.univ.filter (fun y : Block => codeBasisWord e i y = 1), y) = 0 at hm
  rw [← hm]
  apply Finset.sum_bij (fun v _ => label v)
  · intro v hv
    have hvi := (Finset.mem_filter.mp hv).2
    have hh := (hl v (hneq v hvi) (label v)).mpr rfl
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (congrFun hh i).trans hvi⟩
  · intro u hu v hv huv
    have hue := (hl u (hneq u (Finset.mem_filter.mp hu).2) (label u)).mpr rfl
    have hve := (hl v (hneq v (Finset.mem_filter.mp hv).2) (label v)).mpr rfl
    exact hue.symm.trans ((congrArg (codeEvaluation e) huv).trans hve)
  · intro y hy
    let v := codeEvaluation e y
    have hvi : v i = 1 := (Finset.mem_filter.mp hy).2
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩, ?_⟩
    exact ((hl v (hneq v hvi) y).mp rfl).symm
  · intro v hv
    rfl

end BooleanANF
