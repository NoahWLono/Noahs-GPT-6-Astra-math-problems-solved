import HalfRankAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Basic

namespace APNRedo
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev Bilin (E : Type*) [AddCommGroup E] [Module F E] := E →ₗ[F] E →ₗ[F] F

section
variable {E U : Type*} [AddCommGroup E] [Module F E] [Nontrivial E]
  [AddCommGroup U] [Module F U]
theorem binary_add_self (x : E) : x+x=0 := by
  rw [← two_smul F x, (CharTwo.two_eq_zero (R:=F)), zero_smul]

instance endCharTwo : CharP (Module.End F E) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    rw [← (one_add_one_eq_two (R:=Module.End F E))]
    ext x
    change x+x=0
    exact binary_add_self x)

theorem square_add_of_commute (a b : Module.End F E) (h : a*b=b*a) :
    (a+b)*(a+b)=a*a+b*b := by
  calc
    (a+b)*(a+b) = a*a+(a*b+b*a)+b*b := by noncomm_ring
    _ = a*a+b*b := by rw [h, CharTwo.add_self_eq_zero]; simp

/-- A linear family of directions of an affine family of projections squares
linearly and commutes with the base projection. -/
def squaredDirections (t : Module.End F E) (S : U →ₗ[F] Module.End F E)
    (ht : t*t=t) (h : ∀u, (t+S u)*(t+S u)=t+S u) : U →ₗ[F] Module.End F E where
  toFun u := S u * S u
  map_add' u v := by
    rw [map_add]
    apply square_add_of_commute
    apply affine_idempotent_directions_commute t (S u) (S v) ht (h u) (h v)
    simpa only [map_add] using h (u+v)
  map_smul' c u := by
    have hc : c=0 ∨ c=1 := by
      have hc := ZMod.val_lt c
      have hc' : c.val=0 ∨ c.val=1 := by omega
      rcases hc' with hc' | hc'
      · left; exact ZMod.val_injective 2 (by simpa using hc')
      · right; exact ZMod.val_injective 2 (by simpa using hc')
    rcases hc with rfl | rfl <;> simp

theorem squaredDirections_apply (t : Module.End F E)
    (S : U →ₗ[F] Module.End F E) (ht : t*t=t)
    (h : ∀u, (t+S u)*(t+S u)=t+S u) (u : U) :
    squaredDirections t S ht h u = S u * S u := rfl

/-- The square of each direction preserves the kernel of the base projection. -/
theorem square_preserves_kernel (t : Module.End F E) (S : U →ₗ[F] Module.End F E)
    (ht : t*t=t) (h : ∀u, (t+S u)*(t+S u)=t+S u)
    (u : U) (x : E) (hx : t x=0) : t ((S u*S u) x)=0 := by
  have he := LinearMap.congr_fun (affine_idempotent_square_commutes t (S u) ht (h u)) x
  change t ((S u*S u) x)=(S u*S u) (t x) at he
  simpa only [hx,map_zero] using he

def SelfAdjoint (J : Bilin E) (q : Module.End F E) : Prop :=
  ∀x y, J (q x) y=J x (q y)

def Nondegenerate (J : Bilin E) : Prop :=
  ∀x, (∀y, J x y=0) → x=0

/-- The kernel of a selfadjoint projection is nondegenerate for the original form. -/
theorem kernel_nondegenerate (J : Bilin E) (t : Module.End F E)
    (hJ : Nondegenerate J) (ht : t*t=t) (hself : SelfAdjoint J t)
    (x : E) (hx : t x=0)
    (horth : ∀ y, t y=0 → J x y=0) : x=0 := by
  apply hJ x
  intro y
  have hty : t (t y)=t y := LinearMap.congr_fun ht y
  have hym : t (y-t y)=0 := by rw [map_sub,hty,sub_self]
  have hxy := horth (y-t y) hym
  have hxt : J x (t y)=0 := by rw [←hself,hx]; simp
  simpa only [map_sub,hxt,sub_zero] using hxy

/-- The actual restricted squared pencil, rather than an abstract degree predicate. -/
def restrictedSquarePencil (J : Bilin E) (t : Module.End F E)
    (S : U →ₗ[F] Module.End F E) (ht : t*t=t)
    (h : ∀u, (t+S u)*(t+S u)=t+S u) :
    U →ₗ[F] ((LinearMap.ker t) →ₗ[F] (LinearMap.ker t) →ₗ[F] F) where
  toFun u := J.compl₁₂
    ((squaredDirections t S ht h u).comp (LinearMap.ker t).subtype)
    (LinearMap.ker t).subtype
  map_add' u v := by
    ext x y
    simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, map_add,
      LinearMap.add_apply]
  map_smul' c u := by
    ext x y
    simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem restrictedSquarePencil_apply (J : Bilin E) (t : Module.End F E)
    (S : U →ₗ[F] Module.End F E) (ht : t*t=t)
    (h : ∀u, (t+S u)*(t+S u)=t+S u)
    (u : U) (x y : LinearMap.ker t) :
    restrictedSquarePencil J t S ht h u x y = J ((S u*S u) x) y := rfl

theorem restrictedSquarePencil_alternating (J : Bilin E) (t : Module.End F E)
    (S : U →ₗ[F] Module.End F E) (ht : t*t=t)
    (h : ∀u, (t+S u)*(t+S u)=t+S u)
    (hAlt : ∀ x, J x x=0) (hself : ∀u, SelfAdjoint J (S u)) :
    ∀u x, restrictedSquarePencil J t S ht h u x x=0 := by
  intro u x
  change J (S u (S u x)) x=0
  rw [hself u]
  exact hAlt _

theorem restrictedSquarePencil_nondegenerate (J : Bilin E) (t : Module.End F E)
    (S : U →ₗ[F] Module.End F E) (ht : t*t=t)
    (h : ∀u, (t+S u)*(t+S u)=t+S u)
    (hJ : Nondegenerate J) (hself : SelfAdjoint J t)
    (hInj : ∀u, u≠0 → Function.Injective (S u)) :
    ∀u, u≠0 → ∀x, (∀y, restrictedSquarePencil J t S ht h u x y=0) → x=0 := by
  intro u hu x hx
  have hk := square_preserves_kernel t S ht h u (x:E) x.property
  have hz : (S u*S u) (x:E)=0 := by
    apply kernel_nondegenerate J t hJ ht hself _ hk
    intro y hy
    exact hx ⟨y,hy⟩
  have hx0 : (x:E)=0 := by
    apply hInj u hu
    apply hInj u hu
    simpa only [map_zero] using hz
  exact Subtype.ext hx0

#print axioms restrictedSquarePencil_alternating
#print axioms restrictedSquarePencil_nondegenerate
end
end APNRedo
