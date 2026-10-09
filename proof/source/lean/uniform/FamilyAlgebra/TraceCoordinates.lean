import FamilyAlgebra.ConcreteZeroLocus

namespace FamilyAlgebra.TraceCoordinates
variable {E F : Type*} [Field E] [AddCommGroup F]
abbrev V4 (E : Type*) := Fin 4 → E
abbrev Matrix4 (E : Type*) := Fin 4 → Fin 4 → E

def single (i : Fin 4) (a : E) : V4 E := fun j => if j=i then a else 0

def dot (x y : V4 E) : E := x 0*y 0 + x 1*y 1 + x 2*y 2 + x 3*y 3

def action (K : Matrix4 E) (x : V4 E) : V4 E := fun i => dot (K i) x

def form (T : E →+ F) (K : Matrix4 E) (x y : V4 E) : F :=
  T (dot (action K x) y)

theorem dot_single (x : V4 E) (i : Fin 4) (a : E) : dot x (single i a) = x i*a := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => simp [dot, single]
  | i+4 => omega

theorem action_single (K : Matrix4 E) (j : Fin 4) :
    action K (single j 1) = fun i => K i j := by
  funext i
  simp [action, dot_single]

theorem matrix_entry (T : E →+ F) (K : Matrix4 E) (i j : Fin 4) (b : E) :
    form T K (single j 1) (single i b) = T (K i j*b) := by
  simp [form, action_single, dot_single]

/-- Every nonzero additive functional on a field gives a nondegenerate
multiplication pairing. No assertion that the field trace is nonzero is assumed
silently: that is exactly the explicit `nonzero` hypothesis below. -/
theorem separating (T : E →+ F) (nonzero : T ≠ 0) (c : E)
    (h : ∀ b, T (c*b)=0) : c=0 := by
  classical
  by_contra hc
  apply nonzero
  ext z
  have hz := h (c⁻¹*z)
  simpa [← mul_assoc, hc] using hz

/-- The radical of the transferred form is exactly the kernel of K,
expressed pointwise in four coordinates. -/
theorem radical_iff (T : E →+ F) (nonzero : T ≠ 0) (K : Matrix4 E) (x : V4 E) :
    (∀ y, form T K x y=0) ↔ ∀ i, action K x i=0 := by
  constructor
  · intro h i
    apply separating T nonzero
    intro b
    simpa only [form, dot_single] using h (single i b)
  · intro h y
    simp [form, dot, h]

/-- Transfer through a nonzero additive functional is injective on the entire
space of four-by-four field matrices, hence also on an alternating pencil. -/
theorem transfer_injective (T : E →+ F) (nonzero : T ≠ 0) :
    Function.Injective (form T : Matrix4 E → V4 E → V4 E → F) := by
  intro K L h
  funext i j
  apply sub_eq_zero.mp
  apply separating T nonzero
  intro b
  have he : form T K (single j 1) (single i b) = form T L (single j 1) (single i b) :=
    congrFun (congrFun h (single j 1)) (single i b)
  rw [matrix_entry, matrix_entry] at he
  rw [sub_mul, map_sub, he, sub_self]

#print axioms radical_iff
#print axioms transfer_injective
end FamilyAlgebra.TraceCoordinates
