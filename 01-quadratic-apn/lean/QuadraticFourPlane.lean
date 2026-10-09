import QuadraticFourSupport
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Pi

namespace BooleanANF.QuadraticFour

theorem vec_add_self (x : V) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

theorem vec_neg_eq (x : V) : -x = x := by
  ext i
  exact CharTwo.neg_eq (x i)

/-- An ordinary linear parametrization by a binary two-dimensional vector space. -/
def planeMap (u v : V) : (Fin 2 → F₂) →ₗ[F₂] V where
  toFun t := t 0 • u + t 1 • v
  map_add' t s := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c t := by simp [smul_add, mul_smul]

theorem planeMap_injective {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Function.Injective (planeMap u v) := by
  have hs : u + v ≠ 0 := by simpa [add_eq_zero_iff_eq_neg, vec_neg_eq] using huv
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro t ht
  generalize h0 : t 0 = z0 at *
  generalize h1 : t 1 = z1 at *
  fin_cases z0 <;> fin_cases z1 <;>
    simp_all [planeMap]
  ext i
  fin_cases i <;> simp_all

/-- A weight-four quadratic is the indicator of an actual injective affine
image of F₂², not merely a cardinality-four abstract set. -/
theorem weight_four_affine_plane {f : V → F₂} (hf : HasDegreeLE f 2)
    (hw : weight f = 4) :
    ∃ (p : V) (L : (Fin 2 → F₂) →ₗ[F₂] V), Function.Injective L ∧
      ∀ x, f x = 1 ↔ ∃ t, x = p + L t := by
  obtain ⟨a,b,c,hab,hac,hbc,hs⟩ := support_four_parallelogram hf hw
  have hu : a+b ≠ 0 := by simpa [add_eq_zero_iff_eq_neg, vec_neg_eq] using hab
  have hv : a+c ≠ 0 := by simpa [add_eq_zero_iff_eq_neg, vec_neg_eq] using hac
  have huv : a+b ≠ a+c := fun h => hbc (add_left_cancel h)
  refine ⟨a, planeMap (a+b) (a+c), planeMap_injective hu hv huv, ?_⟩
  intro x
  have hm : f x = 1 ↔ x ∈ supportPoints f := by simp [supportPoints]
  rw [hm, hs]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx with hx | hx | hx | hx
    · subst x
      exact ⟨![0,0], by simp [planeMap]⟩
    · subst x
      refine ⟨![1,0], ?_⟩
      simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, zero_smul, one_smul, add_zero, zero_add]
      rw [← add_assoc, vec_add_self, zero_add]
    · subst x
      refine ⟨![0,1], ?_⟩
      simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, zero_smul, one_smul, add_zero, zero_add]
      rw [← add_assoc, vec_add_self, zero_add]
    · subst x
      refine ⟨![1,1], ?_⟩
      simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, zero_smul, one_smul, add_zero, zero_add]
      calc
        a+b+c = (a+a)+a+b+c := by rw [vec_add_self, zero_add]
        _ = a + ((a+b)+(a+c)) := by abel
  · rintro ⟨t, rfl⟩
    generalize h0 : t 0 = z0 at *
    generalize h1 : t 1 = z1 at *
    fin_cases z0 <;> fin_cases z1 <;> simp [planeMap, h0, h1]
    · right; right; left
      rw [← add_assoc, vec_add_self, zero_add]
    · right; left
      rw [← add_assoc, vec_add_self, zero_add]
    · right; right; right
      calc
        a + ((a+b)+(a+c)) = (a+a)+a+b+c := by abel
        _ = a+b+c := by rw [vec_add_self, zero_add]

#print axioms weight_four_affine_plane
end BooleanANF.QuadraticFour
