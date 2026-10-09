import BooleanANF
import PfaffianLaplace2
import QuadraticIndicator.QuadraticIndicator

namespace PfaffianEight
open BooleanANF
abbrev Mat := Matrix (Fin 8) (Fin 8) F
abbrev Vec := Fin 8 → F
abbrev Matching := QuadraticIndicator.Matching

def matchingValue (A : Mat) (m : Matching) : F :=
  (A m.1.1 m.1.2 * A m.2.1.1 m.2.1.2) *
  (A m.2.2.1.1 m.2.2.1.2 * A m.2.2.2.1 m.2.2.2.2)

/-- The canonical sum of the 105 four-edge perfect matchings. -/
def pfaffian (A : Mat) : F :=
  (QuadraticIndicator.matchings.map (matchingValue A)).sum

theorem degree_list_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (l : List α) (f : α → (ι → F) → F) (d : ℕ)
    (hf : ∀ a ∈ l, HasDegreeLE (f a) d) :
    HasDegreeLE (fun x => (l.map (fun a => f a x)).sum) d := by
  induction l with
  | nil => simpa using degree_zero (ι := ι) d
  | cons a l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hf a (by simp)).add (ih (fun b hb => hf b (by simp [hb])))

def pencil (c : Fin 8 → Fin 8 → Fin 8 → F) (b : Vec) : Mat :=
  fun i j => ∑ k, c i j k * b k

theorem degree_pencil_entry (c : Fin 8 → Fin 8 → Fin 8 → F) (i j : Fin 8) :
    HasDegreeLE (fun b => pencil c b i j) 1 := by
  exact HasDegreeLE.sum Finset.univ (fun k b => c i j k * b k) 1
    (fun k _ => (degree_coordinate k).smul (c i j k))

theorem degree_matching_pencil (c : Fin 8 → Fin 8 → Fin 8 → F) (m : Matching) :
    HasDegreeLE (fun b => matchingValue (pencil c b) m) 4 := by
  exact ((degree_pencil_entry c m.1.1 m.1.2).mul
    (degree_pencil_entry c m.2.1.1 m.2.1.2)).mul
    ((degree_pencil_entry c m.2.2.1.1 m.2.2.1.2).mul
      (degree_pencil_entry c m.2.2.2.1 m.2.2.2.2))

/-- Canonical Boolean ANF degree, not merely a syntactic degree certificate. -/
theorem degree_pfaffian_pencil (c : Fin 8 → Fin 8 → Fin 8 → F) :
    HasDegreeLE (fun b => pfaffian (pencil c b)) 4 := by
  exact degree_list_sum QuadraticIndicator.matchings
    (fun m b => matchingValue (pencil c b) m) 4
    (fun m _ => degree_matching_pencil c m)

theorem degree_one_add_pfaffian_pencil (c : Fin 8 → Fin 8 → Fin 8 → F) :
    HasDegreeLE (fun b => 1 + pfaffian (pencil c b)) 4 := by
  exact ((degree_const 1).mono (by omega)).add (degree_pfaffian_pencil c)

theorem linear_pencil_eq (L : Vec →ₗ[F] Mat) (b : Vec) :
    L b = pencil (fun i j k => L (Pi.single k 1) i j) b := by
  have hb : b = ∑ k : Fin 8, b k • (Pi.single k (1 : F) : Vec) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  calc
    L b = L (∑ k : Fin 8, b k • (Pi.single k (1 : F) : Vec)) := congrArg L hb
    _ = ∑ k : Fin 8, b k • L (Pi.single k (1 : F)) := by simp
    _ = pencil (fun i j k => L (Pi.single k 1) i j) b := by
      ext i j
      simp only [pencil, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _

theorem degree_pfaffian_linear (L : Vec →ₗ[F] Mat) :
    HasDegreeLE (fun b => pfaffian (L b)) 4 := by
  have h := degree_pfaffian_pencil (fun i j k => L (Pi.single k 1) i j)
  simpa only [← linear_pencil_eq L] using h

#print axioms degree_pfaffian_linear
#print axioms degree_pfaffian_pencil
end PfaffianEight
