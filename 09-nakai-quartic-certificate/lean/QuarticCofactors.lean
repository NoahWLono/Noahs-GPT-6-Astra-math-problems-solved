import QuarticDefinitions
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- The diagonal part of the Hessian in its diagonal-plus-rank-one expression. -/
def D (i : Fin 4) : P := 2 * S + 6 * x i ^ 2

def C₀ : Matrix (Fin 4) (Fin 4) P := !![
  D 1 * D 2 * D 3 + 4 * x 1 ^ 2 * D 2 * D 3 + 4 * x 2 ^ 2 * D 1 * D 3 + 4 * x 3 ^ 2 * D 1 * D 2,
  -4 * x 0 * x 1 * D 2 * D 3, -4 * x 0 * x 2 * D 1 * D 3, -4 * x 0 * x 3 * D 1 * D 2;
  -4 * x 0 * x 1 * D 2 * D 3,
  D 0 * D 2 * D 3 + 4 * x 0 ^ 2 * D 2 * D 3 + 4 * x 2 ^ 2 * D 0 * D 3 + 4 * x 3 ^ 2 * D 0 * D 2,
  -4 * x 1 * x 2 * D 0 * D 3, -4 * x 1 * x 3 * D 0 * D 2;
  -4 * x 0 * x 2 * D 1 * D 3, -4 * x 1 * x 2 * D 0 * D 3,
  D 0 * D 1 * D 3 + 4 * x 0 ^ 2 * D 1 * D 3 + 4 * x 1 ^ 2 * D 0 * D 3 + 4 * x 3 ^ 2 * D 0 * D 1,
  -4 * x 2 * x 3 * D 0 * D 1;
  -4 * x 0 * x 3 * D 1 * D 2, -4 * x 1 * x 3 * D 0 * D 2, -4 * x 2 * x 3 * D 0 * D 1,
  D 0 * D 1 * D 2 + 4 * x 0 ^ 2 * D 1 * D 2 + 4 * x 1 ^ 2 * D 0 * D 2 + 4 * x 2 ^ 2 * D 0 * D 1]

/-- Keep the diagonal variables factored when expanding the minors. -/
theorem H₀_entry (i j : Fin 4) : H₀ i j =
    if i = j then D i + 4 * x i ^ 2 else 4 * x i * x j := by
  by_cases hij : i = j
  · subst j
    simp only [H₀, if_pos rfl, D]
    ring
  · simp only [H₀, if_neg hij]

/-- The twelve deletion-index values are kernel-reduced before polynomial algebra. -/
theorem succAbove4_table (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![1,2,3; 0,2,3; 0,1,3; 0,1,2] : Matrix (Fin 4) (Fin 3) (Fin 4)) i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- A scalar ring identity shared by all four diagonal cofactors. -/
theorem diagonal_cofactor_identity {R : Type*} [CommRing R] (d e f u v w : R) :
    (d + 4*u^2) * (e + 4*v^2) * (f + 4*w^2)
      - (d + 4*u^2) * (4*v*w) * (4*w*v)
      - (4*u*v) * (4*v*u) * (f + 4*w^2)
      + (4*u*v) * (4*v*w) * (4*w*u)
      + (4*u*w) * (4*v*u) * (4*w*v)
      - (4*u*w) * (e + 4*v^2) * (4*w*u) =
        d*e*f + 4*u^2*e*f + 4*v^2*d*f + 4*w^2*d*e := by ring

theorem C00_factored : C 0 0 = C₀ 0 0 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  exact diagonal_cofactor_identity (D 1) (D 2) (D 3) (x 1) (x 2) (x 3)

#print axioms NakaiQuartic.C00_factored

theorem C01_factored : C 0 1 = C₀ 0 1 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C01_factored

theorem C02_factored : C 0 2 = C₀ 0 2 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C02_factored

theorem C03_factored : C 0 3 = C₀ 0 3 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C03_factored

theorem C10_factored : C 1 0 = C₀ 1 0 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C10_factored

theorem C11_factored : C 1 1 = C₀ 1 1 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  exact diagonal_cofactor_identity (D 0) (D 2) (D 3) (x 0) (x 2) (x 3)

#print axioms NakaiQuartic.C11_factored

theorem C12_factored : C 1 2 = C₀ 1 2 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C12_factored

theorem C13_factored : C 1 3 = C₀ 1 3 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C13_factored

theorem C20_factored : C 2 0 = C₀ 2 0 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C20_factored

theorem C21_factored : C 2 1 = C₀ 2 1 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C21_factored

theorem C22_factored : C 2 2 = C₀ 2 2 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  exact diagonal_cofactor_identity (D 0) (D 1) (D 3) (x 0) (x 1) (x 3)

#print axioms NakaiQuartic.C22_factored

theorem C23_factored : C 2 3 = C₀ 2 3 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C23_factored

theorem C30_factored : C 3 0 = C₀ 3 0 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C30_factored

theorem C31_factored : C 3 1 = C₀ 3 1 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C31_factored

theorem C32_factored : C 3 2 = C₀ 3 2 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.C32_factored

theorem C33_factored : C 3 3 = C₀ 3 3 := by
  rw [C_formula]
  simp only [succAbove4_table]
  norm_num [C₀, H₀_entry, Fin.ext_iff]
  exact diagonal_cofactor_identity (D 0) (D 1) (D 2) (x 0) (x 1) (x 2)

#print axioms NakaiQuartic.C33_factored

/-- Every actual cofactor is identified with a compact polynomial expression once. -/
theorem C_factored (i j : Fin 4) : C i j = C₀ i j := by
  fin_cases i <;> fin_cases j
  · exact C00_factored
  · exact C01_factored
  · exact C02_factored
  · exact C03_factored
  · exact C10_factored
  · exact C11_factored
  · exact C12_factored
  · exact C13_factored
  · exact C20_factored
  · exact C21_factored
  · exact C22_factored
  · exact C23_factored
  · exact C30_factored
  · exact C31_factored
  · exact C32_factored
  · exact C33_factored

#print axioms NakaiQuartic.C_factored
end NakaiQuartic
