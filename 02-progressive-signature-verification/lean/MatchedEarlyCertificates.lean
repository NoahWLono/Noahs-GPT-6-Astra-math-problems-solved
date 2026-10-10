import ParameterCertificate
import CostAndConfidence

/-! Exact arithmetic certificates for the inspected row-dot-product baselines.
These do not formalize Reed--Solomon coding theory or assert a lower bound for
all alternative verification algorithms. The RS comparator's published/code-
distance premise is a nonzero residual with at most 1023 zero coordinates. -/
namespace ProgressivePool.MatchedEarlyCertificates

 theorem rs_storage_ceiling :
    1154*61852 ≤ 71384576 ∧ 71384576 < 1155*61852 := by norm_num

/-- Without-replacement RS row checks: the first six target confidence levels
require at least these counts under the worst-case 1023-zero-row profile. -/
 theorem rs_early_thresholds :
    2^1 * Nat.descFactorial 1023 5 > Nat.descFactorial 1154 5 ∧
    2^1 * Nat.descFactorial 1023 6 ≤ Nat.descFactorial 1154 6 ∧
    2^2 * Nat.descFactorial 1023 11 > Nat.descFactorial 1154 11 ∧
    2^2 * Nat.descFactorial 1023 12 ≤ Nat.descFactorial 1154 12 ∧
    2^3 * Nat.descFactorial 1023 17 > Nat.descFactorial 1154 17 ∧
    2^3 * Nat.descFactorial 1023 18 ≤ Nat.descFactorial 1154 18 ∧
    2^4 * Nat.descFactorial 1023 22 > Nat.descFactorial 1154 22 ∧
    2^4 * Nat.descFactorial 1023 23 ≤ Nat.descFactorial 1154 23 ∧
    2^5 * Nat.descFactorial 1023 28 > Nat.descFactorial 1154 28 ∧
    2^5 * Nat.descFactorial 1023 29 ≤ Nat.descFactorial 1154 29 ∧
    2^6 * Nat.descFactorial 1023 33 > Nat.descFactorial 1154 33 ∧
    2^6 * Nat.descFactorial 1023 34 ≤ Nat.descFactorial 1154 34 := by
  norm_num [Nat.descFactorial]

/-- The matched terminal comparator uses seven rows, not 128 rows. -/
 theorem terminal_work : (7*(61852+1024) : ℕ) = 440132 := by norm_num

#print axioms rs_storage_ceiling
#print axioms rs_early_thresholds
#print axioms terminal_work
end ProgressivePool.MatchedEarlyCertificates
