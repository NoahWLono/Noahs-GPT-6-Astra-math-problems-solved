import NakaiFramework
import QuarticDefinitions

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace NakaiQuartic
open NakaiFramework

theorem QP_orderLE2 : IsOrderLE2 QP := by
  have heq : QP =
      ((∑ i : Fin 4, ∑ j : Fin 4,
        mulEnd (B i j) * (pderiv i).toLinearMap * (pderiv j).toLinearMap) +
        ∑ i : Fin 4, mulEnd (6 * a i) * (pderiv i).toLinearMap) := by
    apply LinearMap.ext
    intro p
    simp only [QP_apply, LinearMap.add_apply, LinearMap.sum_apply,
      Module.End.mul_apply, mulEnd_apply, Derivation.coeFn_coe,
      Fin.sum_univ_four]
    ring
  rw [heq]
  exact orderLE2_secondOrder B (fun i => 6 * a i) (fun i => pderiv i)

#print axioms NakaiQuartic.QP_orderLE2

end NakaiQuartic
