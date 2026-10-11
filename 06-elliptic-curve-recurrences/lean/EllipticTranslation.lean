import EllipticInfinity
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Translation of the actual generic point of a nonsingular Weierstrass curve.
This module begins the function-field translation construction. It does not
assume valuation covariance or the obstruction theorem. -/
namespace Astra01.EllipticTranslation
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField.Chart
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]

local instance : DecidableEq k := Classical.decEq _
local instance : DecidableEq K := Classical.decEq _
local instance : (W⁄K).IsElliptic := inferInstanceAs (W.map (algebraMap k K)).IsElliptic

def genericPoint : (W⁄K).Point :=
  .some (XK k K) (W.yCoord K)
    ((W⁄K).equation_iff_nonsingular.mp (yCoord_equation W K))

def constantPoint : W.Point →+ (W⁄K).Point := Point.baseChange (W' := W) k K

include W in
theorem generic_x_ne_constant (c : k) : XK k K ≠ algebraMap k K c := by
  intro h
  have hx : XK k K = algebraMap k[X] K Polynomial.X := by
    rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
    rfl
  rw [hx, IsScalarTower.algebraMap_apply k k[X] K] at h
  have hpoly := W.algebraMap_polynomial_injective K h
  exact Polynomial.X_ne_C c hpoly

theorem genericPoint_ne_constant (P : W.Point) :
    genericPoint W K ≠ constantPoint W K P := by
  cases P with
  | zero => simp [genericPoint, constantPoint, Point.baseChange, Point.map]
  | some x y h =>
    intro heq
    exact generic_x_ne_constant W K x (Point.some.inj heq).1

def translatedPoint (G : W.Point) : (W⁄K).Point :=
  genericPoint W K + constantPoint W K G

theorem translatedPoint_ne_constant (G P : W.Point) :
    translatedPoint W K G ≠ constantPoint W K P := by
  intro h
  apply genericPoint_ne_constant W K (P - G)
  rw [map_sub]
  exact eq_sub_iff_add_eq.mpr h

theorem translatedPoint_ne_zero (G : W.Point) : translatedPoint W K G ≠ 0 := by
  simpa only [map_zero] using translatedPoint_ne_constant W K G 0

variable [IsAlgClosed k]

/-- Algebraic closedness is used only for a single integral element, not for
an assumed algebraic extension of the whole function field. -/
theorem integral_eq_constant {y : K} (hy : IsIntegral k y) :
    ∃ c : k, algebraMap k K c = y := by
  refine ⟨-(minpoly k y).coeff 0, ?_⟩
  have hq : (minpoly k y).leadingCoeff = 1 := minpoly.monic hy
  have hd : (minpoly k y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hy)
  have he := minpoly.aeval k y
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hq, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  simpa only [map_neg] using he.symm

theorem y_eq_constant_of_x_constant (c : k) (y : K)
    (he : (W⁄K).Equation (algebraMap k K c) y) :
    ∃ d : k, algebraMap k K d = y := by
  apply integral_eq_constant K
  let p : k[X] := W.polynomial.map (Polynomial.evalRingHom c)
  refine ⟨p, W.monic_polynomial.map _, ?_⟩
  have h := (W⁄K).equation_iff' _ _ |>.mp he
  simpa [p, polynomial, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    Polynomial.evalRingHom, map_add, map_mul, map_pow, map_sub, add_mul, add_assoc] using h

theorem some_eq_constant_of_x_constant (c : k) (y : K)
    (h : (W⁄K).Nonsingular (algebraMap k K c) y) :
    ∃ P : W.Point, Point.some _ _ h = constantPoint W K P := by
  obtain ⟨d, hd⟩ := y_eq_constant_of_x_constant W K c y h.1
  subst y
  have hd' : W.Nonsingular c d :=
    (W.baseChange_nonsingular (Algebra.ofId k K).injective c d).mp h
  exact ⟨Point.some c d hd', rfl⟩

/-- The translated generic point has nonconstant x-coordinate. This ensures
that substitution into its x-coordinate is injective on the base polynomial ring. -/
theorem translated_x_ne_constant (G : W.Point) {x y : K}
    (h : (W⁄K).Nonsingular x y)
    (hpoint : translatedPoint W K G = Point.some x y h) (c : k) :
    x ≠ algebraMap k K c := by
  intro hx
  subst x
  obtain ⟨P, hP⟩ := some_eq_constant_of_x_constant W K c y h
  exact translatedPoint_ne_constant W K G P (hpoint.trans hP)


def pointCoordinateHom {x y : K} (h : (W⁄K).Equation x y) : W.CoordinateRing →ₐ[k] K :=
  AdjoinRoot.liftAlgHom W.polynomial (Polynomial.aeval x) y (by
    have he := (W⁄K).equation_iff' x y |>.mp h
    simpa [polynomial, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      Polynomial.aeval_def, Polynomial.eval₂_pow, add_mul, add_assoc] using he)

theorem pointCoordinateHom_base {x y : K} (h : (W⁄K).Equation x y) (p : k[X]) :
    pointCoordinateHom W K h (algebraMap k[X] W.CoordinateRing p) =
      Polynomial.aeval x p := AdjoinRoot.liftAlgHom_of _ _ _ _ _

theorem pointCoordinateHom_injective {x y : K} (h : (W⁄K).Equation x y)
    (hx : ∀ c : k, x ≠ algebraMap k K c) :
    Function.Injective (pointCoordinateHom W K h) := by
  have hi : Function.Injective (Polynomial.aeval x : k[X] →ₐ[k] K) :=
    transcendental_iff_injective.mp (by
      intro ha
      obtain ⟨c, hc⟩ := integral_eq_constant K ha.isIntegral
      exact hx c hc.symm)
  rw [injective_iff_map_eq_zero]
  intro r hr
  apply (Algebra.norm_eq_zero_iff (R := k[X])).mp
  apply hi
  rw [map_zero, ← pointCoordinateHom_base W K h]
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [← hpq] at hr ⊢
  change pointCoordinateHom W K h (AdjoinRoot.of W.polynomial
    (Algebra.norm k[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Polynomial.X))) = 0
  rw [CoordinateRing.coe_norm_smul_basis, map_mul]
  have hm : CoordinateRing.mk W (Polynomial.C p + Polynomial.C q * Polynomial.X) =
      p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Polynomial.X := by
    simp [map_add, map_mul, Algebra.smul_def]
  rw [hm, map_mul, hr, zero_mul]

def pointFunctionHom {x y : K} (h : (W⁄K).Equation x y)
    (hx : ∀ c : k, x ≠ algebraMap k K c) : K →ₐ[k] K :=
  IsFractionRing.liftAlgHom (pointCoordinateHom_injective W K h hx)


theorem pointFunctionHom_base {x y : K} (h : (W⁄K).Equation x y)
    (hx : ∀ c : k, x ≠ algebraMap k K c) (r : W.CoordinateRing) :
    pointFunctionHom W K h hx (algebraMap W.CoordinateRing K r) =
      pointCoordinateHom W K h r :=
  IsFractionRing.lift_algebraMap (pointCoordinateHom_injective W K h hx) r

theorem pointFunctionHom_generic {x y : K} (h : (W⁄K).Nonsingular x y)
    (hx : ∀ c : k, x ≠ algebraMap k K c) :
    Point.map (pointFunctionHom W K h.1 hx) (genericPoint W K) = Point.some x y h := by
  simp only [genericPoint, Point.map_some, Point.some.injEq]
  constructor
  · change pointFunctionHom W K h.1 hx (XK k K) = x
    rw [← xCoord_eq_XK W K, pointFunctionHom_base]
    change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.mk _ _) = x
    rw [AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_C]
    exact Polynomial.aeval_X x
  · change pointFunctionHom W K h.1 hx (W.yCoord K) = y
    rw [WeierstrassCurve.Affine.yCoord, pointFunctionHom_base]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem exists_translationHom (G : W.Point) :
    ∃ f : K →ₐ[k] K, Point.map f (genericPoint W K) = translatedPoint W K G := by
  cases hp : translatedPoint W K G with
  | zero => exact False.elim (translatedPoint_ne_zero W K G hp)
  | some x y h =>
    exact ⟨pointFunctionHom W K h.1 (translated_x_ne_constant W K G h hp),
      pointFunctionHom_generic W K h (translated_x_ne_constant W K G h hp)⟩

/-- Pullback by the genuine curve translation P ↦ P + G, constructed from its
values on the generic point rather than postulated as an automorphism. -/
def translationHom (G : W.Point) : K →ₐ[k] K :=
  (exists_translationHom W K G).choose

theorem translationHom_generic (G : W.Point) :
    Point.map (translationHom W K G) (genericPoint W K) =
      genericPoint W K + constantPoint W K G :=
  (exists_translationHom W K G).choose_spec


theorem functionHom_ext {f g : K →ₐ[k] K}
    (h : Point.map f (genericPoint W K) = Point.map g (genericPoint W K)) : f = g := by
  have hxy := Point.some.inj h
  apply IsLocalization.algHom_ext (nonZeroDivisors W.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change f (algebraMap W.CoordinateRing K
      (CoordinateRing.mk W (Polynomial.C Polynomial.X))) =
      g (algebraMap W.CoordinateRing K (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
    rw [xCoord_eq_XK W K]
    exact hxy.1
  · exact hxy.2

theorem map_constantPoint (f : K →ₐ[k] K) (P : W.Point) :
    Point.map f (constantPoint W K P) = constantPoint W K P :=
  Point.map_baseChange (W' := W) f P

theorem translationHom_add (G H : W.Point) :
    (translationHom W K G).comp (translationHom W K H) = translationHom W K (G + H) := by
  apply functionHom_ext W K
  rw [← Point.map_map, translationHom_generic, map_add, translationHom_generic,
    map_constantPoint, translationHom_generic, map_add, add_assoc]

theorem translationHom_zero : translationHom W K 0 = AlgHom.id k K := by
  apply functionHom_ext W K
  rw [translationHom_generic, map_zero, add_zero]
  exact (Point.map_id _).symm


/-- Actual function-field automorphism induced by translation on the curve. -/
def translationEquiv (G : W.Point) : K ≃ₐ[k] K :=
  AlgEquiv.ofAlgHom (translationHom W K G) (translationHom W K (-G))
    (by rw [translationHom_add, add_neg_cancel, translationHom_zero])
    (by rw [translationHom_add, neg_add_cancel, translationHom_zero])

theorem translationEquiv_generic (G : W.Point) :
    Point.map (translationEquiv W K G).toAlgHom (genericPoint W K) =
      genericPoint W K + constantPoint W K G := translationHom_generic W K G

theorem translationEquiv_injective : Function.Injective (translationEquiv W K) := by
  intro G H h
  have hp := congrArg (fun e : K ≃ₐ[k] K => Point.map e.toAlgHom (genericPoint W K)) h
  rw [translationEquiv_generic, translationEquiv_generic, add_right_inj] at hp
  exact Point.map_injective (W' := W) (Algebra.ofId k K) hp

end
end Astra01.EllipticTranslation
#print axioms Astra01.EllipticTranslation.translatedPoint_ne_zero

#print axioms Astra01.EllipticTranslation.translated_x_ne_constant

#print axioms Astra01.EllipticTranslation.pointFunctionHom

#print axioms Astra01.EllipticTranslation.translationHom_generic

#print axioms Astra01.EllipticTranslation.translationHom_add

#print axioms Astra01.EllipticTranslation.translationEquiv
#print axioms Astra01.EllipticTranslation.translationEquiv_generic
#print axioms Astra01.EllipticTranslation.translationEquiv_injective
