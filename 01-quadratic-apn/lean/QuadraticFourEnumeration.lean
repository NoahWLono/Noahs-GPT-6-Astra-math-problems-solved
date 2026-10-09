import QuadraticFourBatch0
import QuadraticFourBatch1
import QuadraticFourBatch2
import QuadraticFourBatch3
import QuadraticFourBatch4
import QuadraticFourBatch5
import QuadraticFourBatch6
import QuadraticFourBatch7
namespace QuadraticFourRaw
theorem all_weights : ∀ a b c d e f g h i j k : F,
    weight (poly a b c d e f g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by
  intro a b c d e f
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f
  · exact weights000000
  · exact weights000001
  · exact weights000010
  · exact weights000011
  · exact weights000100
  · exact weights000101
  · exact weights000110
  · exact weights000111
  · exact weights001000
  · exact weights001001
  · exact weights001010
  · exact weights001011
  · exact weights001100
  · exact weights001101
  · exact weights001110
  · exact weights001111
  · exact weights010000
  · exact weights010001
  · exact weights010010
  · exact weights010011
  · exact weights010100
  · exact weights010101
  · exact weights010110
  · exact weights010111
  · exact weights011000
  · exact weights011001
  · exact weights011010
  · exact weights011011
  · exact weights011100
  · exact weights011101
  · exact weights011110
  · exact weights011111
  · exact weights100000
  · exact weights100001
  · exact weights100010
  · exact weights100011
  · exact weights100100
  · exact weights100101
  · exact weights100110
  · exact weights100111
  · exact weights101000
  · exact weights101001
  · exact weights101010
  · exact weights101011
  · exact weights101100
  · exact weights101101
  · exact weights101110
  · exact weights101111
  · exact weights110000
  · exact weights110001
  · exact weights110010
  · exact weights110011
  · exact weights110100
  · exact weights110101
  · exact weights110110
  · exact weights110111
  · exact weights111000
  · exact weights111001
  · exact weights111010
  · exact weights111011
  · exact weights111100
  · exact weights111101
  · exact weights111110
  · exact weights111111
end QuadraticFourRaw
