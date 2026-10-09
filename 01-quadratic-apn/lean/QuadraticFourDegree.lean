import QuadraticFourPolynomial

namespace BooleanANF.QuadraticFour

theorem eval_degree (c : Coeff) : HasDegreeLE (eval c) 2 := by
  apply HasDegreeLE.sum
  intro i hi
  exact ((degree_monomial (indices i)).mono ((indices_cover (indices i)).mpr ⟨i,rfl⟩)).smul (c i)

theorem poly_degree (a b c d e f g h i j k : F₂) :
    HasDegreeLE (poly a b c d e f g h i j k) 2 := by
  simpa only [eval_eq_poly, Matrix.cons_val_zero, Matrix.cons_val_succ] using
    eval_degree ![a,b,c,d,e,f,g,h,i,j,k]

end BooleanANF.QuadraticFour
