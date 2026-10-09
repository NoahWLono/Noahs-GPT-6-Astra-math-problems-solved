import BooleanANFWeight

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace BooleanANF.QuadraticFour
open scoped BigOperators
abbrev V := Fin 4 → F₂
abbrev Coeff := Fin 11 → F₂

def indices : Fin 11 → Finset (Fin 4) :=
  ![∅, {0}, {1}, {2}, {3}, {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]

def eval (c : Coeff) (x : V) : F₂ :=
  ∑ i, c i * monomial (indices i) x

theorem indices_injective : Function.Injective indices := by decide

theorem indices_cover : ∀ s : Finset (Fin 4), s.card ≤ 2 ↔ ∃ i, indices i = s := by decide

theorem representation {f : V → F₂} (hf : HasDegreeLE f 2) :
    eval (fun i => coefficient f (indices i)) = f := by
  funext x
  rw [← reconstruction_all f x]
  unfold eval
  apply Finset.sum_bij_ne_zero (fun i _ _ => indices i)
  · intro i hi hn
    exact Finset.mem_univ _
  · intro i hi hn j hj hm h
    exact indices_injective h
  · intro s hs hn
    have hc : s.card ≤ 2 := by
      by_contra h
      have hz := hf s (by omega)
      simp [hz] at hn
    obtain ⟨i, hi⟩ := (indices_cover s).mp hc
    exact ⟨i, Finset.mem_univ _, by simpa [hi] using hn, hi⟩
  · intro i hi hn
    rfl


end BooleanANF.QuadraticFour
