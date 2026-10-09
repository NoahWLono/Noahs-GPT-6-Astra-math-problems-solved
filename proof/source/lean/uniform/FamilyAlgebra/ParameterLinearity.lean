import FamilyAlgebra.BinaryCoordinates
import FamilyAlgebra.ParameterData
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases

namespace FamilyAlgebra
variable {E : Type*} [Field E]

theorem base_add : ∀ u v w z u' v' w' z',
    base (u ^^ u') (v ^^ v') (w ^^ w') (z ^^ z') = add (base u v w z) (base u' v' w' z') := by decide

theorem odd_add : ∀ s t s' t', oddPlane (s ^^ s') (t ^^ t')=add (oddPlane s t) (oddPlane s' t') := by decide

theorem even_add : ∀ s t s' t', evenPlane (s ^^ s') (t ^^ t')=add (evenPlane s t) (evenPlane s' t') := by decide

theorem family_add (u v w z u' v' w' z' : Bool) (s t s' t' : Nat → Bool) (j : Nat) :
    family (u ^^ u') (v ^^ v') (w ^^ w') (z ^^ z')
      (fun k => s k ^^ s' k) (fun k => t k ^^ t' k) j =
      add (family u v w z s t j) (family u' v' w' z' s' t' j) := by
  by_cases hj : j=0
  · simp [family, hj, base_add]
  · by_cases ho : j%2=1
    · simp [family, hj, ho, odd_add]
    · simp [family, hj, ho, even_add]

theorem sixCoord_add (x y : Six) (i : Fin 6) :
    sixCoord (add x y) i = (sixCoord x i ^^ sixCoord y i) := by
  rcases i with ⟨i,hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | i+6 => omega

theorem pencil_add (two_zero : (2:E)=0) (a : E) (X Y : Nat → Six) (n : Nat) :
    pencil a (fun j => add (X j) (Y j)) n = pencil a X n + pencil a Y n := by
  funext i
  simp only [pencil_coord, sixCoord_add, binarySum_xor two_zero, Pi.add_apply]

theorem pencil_zero (a : E) (n : Nat) :
    pencil a (fun _ => ⟨false,false,false,false,false,false⟩) n=0 := by
  funext i
  simp [pencil_coord, zeroSix_coord, binarySum_false]

theorem altMatrix_add (x y : Pfaffian.Coordinates E) :
    altMatrix (x+y)=altMatrix x+altMatrix y := by
  funext i j
  simp only [altMatrix, Pi.add_apply]
  split <;> simp

theorem altMatrix_zero : altMatrix (0 : Pfaffian.Coordinates E)=0 := by
  funext i j
  simp only [altMatrix, Pi.zero_apply]
  split <;> rfl


def parameterFamily {n : Nat} (p : Parameters n) : Nat → Six :=
  family (paramRead p 0) (paramRead p 1) (paramRead p 2) (paramRead p 3)
    (fun j => paramRead p (2*j+2)) (fun j => paramRead p (2*j+3))

theorem parameterFamily_add {n : Nat} (p q : Parameters n) :
    parameterFamily (p+q) = fun j => add (parameterFamily p j) (parameterFamily q j) := by
  funext j
  simp only [parameterFamily, paramRead_add, family_add]

theorem parameterFamily_zero (n : Nat) :
    parameterFamily (0 : Parameters n) = fun _ => ⟨false,false,false,false,false,false⟩ := by
  funext j
  simp [parameterFamily, paramRead_zero, family, base, oddPlane, evenPlane]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binaryForm_add (n : Nat) (positive : 0<n)
    (K L : TraceCoordinates.Matrix4 (GaloisField 2 n)) :
    binaryForm n positive (K+L) = binaryForm n positive K + binaryForm n positive L := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change Algebra.trace (ZMod 2) (GaloisField 2 n)
    (TraceCoordinates.dot (TraceCoordinates.action (K+L) ((binaryCoordinates n positive).symm x)) ((binaryCoordinates n positive).symm y)) =
    Algebra.trace (ZMod 2) (GaloisField 2 n)
    (TraceCoordinates.dot (TraceCoordinates.action K ((binaryCoordinates n positive).symm x)) ((binaryCoordinates n positive).symm y)) +
    Algebra.trace (ZMod 2) (GaloisField 2 n)
    (TraceCoordinates.dot (TraceCoordinates.action L ((binaryCoordinates n positive).symm x)) ((binaryCoordinates n positive).symm y))
  have h : TraceCoordinates.dot
      (TraceCoordinates.action (K+L) ((binaryCoordinates n positive).symm x))
      ((binaryCoordinates n positive).symm y) =
      TraceCoordinates.dot (TraceCoordinates.action K ((binaryCoordinates n positive).symm x)) ((binaryCoordinates n positive).symm y) +
      TraceCoordinates.dot (TraceCoordinates.action L ((binaryCoordinates n positive).symm x)) ((binaryCoordinates n positive).symm y) := by
    simp only [TraceCoordinates.dot, TraceCoordinates.action, Pi.add_apply]
    ring
  rw [h, map_add]

theorem binaryForm_zero (n : Nat) (positive : 0<n) : binaryForm n positive 0=0 := by
  ext x y
  simp [binaryForm_apply, TraceCoordinates.form, TraceCoordinates.dot, TraceCoordinates.action]

/-- The actual effective parameter assignment, now as an F2-linear map. -/
noncomputable def linearFamily (n : Nat) (positive : 0<n) (a : GaloisField 2 n) :
    Parameters n →ₗ[ZMod 2] LinearMap.BilinForm (ZMod 2) (Fin (4*n) → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun p => binaryForm n positive (altMatrix (pencil a (parameterFamily p) n))
      map_zero' := by rw [parameterFamily_zero, pencil_zero, altMatrix_zero, binaryForm_zero]
      map_add' := by
        intro p q
        rw [parameterFamily_add, pencil_add (CharP.cast_eq_zero (GaloisField 2 n) 2), altMatrix_add, binaryForm_add] }

theorem linearFamily_apply (n : Nat) (positive : 0<n) (a : GaloisField 2 n) (p : Parameters n) :
    linearFamily n positive a p = binaryForm n positive (altMatrix (pencil a (parameterFamily p) n)) := rfl

theorem linearFamily_alt (n : Nat) (positive : 0<n) (a : GaloisField 2 n) (p : Parameters n) :
    (linearFamily n positive a p).IsAlt := binaryForm_alt n positive _

theorem extension_pairs_iff {n : Nat} (p : Parameters n) :
    (∀ j, 0<j → j<n → paramRead p (2*j+2)=false ∧ paramRead p (2*j+3)=false) ↔
      ∀ k : Fin (2*n+2), 4≤k.val → p k=0 := by
  constructor
  · intro h k hk
    let j := (k.val-2)/2
    have hj : 0<j := by dsimp [j]; omega
    have hjn : j<n := by have := k.isLt; dsimp [j]; omega
    rcases h j hj hjn with ⟨he,ho⟩
    have hread : paramRead p k.val=false := by
      have hcases : k.val=2*j+2 ∨ k.val=2*j+3 := by dsimp [j]; omega
      rcases hcases with hc | hc
      · simpa only [hc] using he
      · simpa only [hc] using ho
    simpa [paramRead, k.isLt, f2Bit] using hread
  · intro h j hj hjn
    have he : 2*j+2<2*n+2 := by omega
    have ho : 2*j+3<2*n+2 := by omega
    have hpe := h ⟨2*j+2,he⟩ (by change 4≤2*j+2; omega)
    have hpo := h ⟨2*j+3,ho⟩ (by change 4≤2*j+3; omega)
    constructor
    · simp [paramRead, he, hpe, f2Bit]
    · simp [paramRead, ho, hpo, f2Bit]

theorem linearFamily_nondegenerate_iff (n : Nat) (positive : 0<n) (a : GaloisField 2 n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (p : Parameters n) :
    (linearFamily n positive a p).Nondegenerate ↔ ¬badParameters n p := by
  change (binaryForm n positive (altMatrix (pencil a (parameterFamily p) n))).Nondegenerate ↔ _
  unfold parameterFamily
  rw [binary_family_nondegenerate_iff n positive a independent, extension_pairs_iff]
  rfl

/-- The unused output masks are literally the final 2n-2 coordinates. -/
def parameterProjection (n : Nat) (positive : 0<n) :
    (Fin (4*n) → ZMod 2) →ₗ[ZMod 2] Parameters n where
  toFun := projectParameters n positive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def fullLinearFamily (n : Nat) (positive : 0<n) (a : GaloisField 2 n) :
    (Fin (4*n) → ZMod 2) →ₗ[ZMod 2] LinearMap.BilinForm (ZMod 2) (Fin (4*n) → ZMod 2) :=
  (linearFamily n positive a).comp (parameterProjection n positive)

theorem fullLinearFamily_alt (n : Nat) (positive : 0<n) (a : GaloisField 2 n)
    (p : Fin (4*n) → ZMod 2) : (fullLinearFamily n positive a p).IsAlt :=
  linearFamily_alt n positive a _

theorem fullLinearFamily_nondegenerate_iff (n : Nat) (positive : 0<n) (a : GaloisField 2 n)
    (independent : ∀ bits, binarySum (fun k => a^k) bits n=0 ↔ ∀ k, k<n → bits k=false)
    (p : Fin (4*n) → ZMod 2) :
    (fullLinearFamily n positive a p).Nondegenerate ↔ ¬badFullMask n positive p :=
  linearFamily_nondegenerate_iff n positive a independent _

theorem realized_fullLinearFamily (n : Nat) (positive : 0<n) :
    ∃ a : GaloisField 2 n, ∀ p : Fin (4*n) → ZMod 2,
      (fullLinearFamily n positive a p).IsAlt ∧
      ((fullLinearFamily n positive a p).Nondegenerate ↔ ¬badFullMask n positive p) := by
  rcases galois_power_basis n positive with ⟨a,ha⟩
  exact ⟨a, fun p => ⟨fullLinearFamily_alt n positive a p,
    fullLinearFamily_nondegenerate_iff n positive a ha p⟩⟩

#print axioms realized_fullLinearFamily
#print axioms linearFamily
#print axioms linearFamily_alt
end FamilyAlgebra
