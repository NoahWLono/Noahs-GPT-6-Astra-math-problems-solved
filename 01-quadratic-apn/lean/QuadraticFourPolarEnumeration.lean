import QuadraticFourPolarBatch0
import QuadraticFourPolarBatch1
import QuadraticFourPolarBatch2
import QuadraticFourPolarBatch3
import QuadraticFourPolarBatch4
import QuadraticFourPolarBatch5
import QuadraticFourPolarBatch6
import QuadraticFourPolarBatch7
namespace QuadraticFourRaw
theorem all_classified : ∀ a b c d e f g h i j k : F,
    classified a b c d e f g h i j k := by
  intro a b c d e f
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f
  · exact classified000000
  · exact classified000001
  · exact classified000010
  · exact classified000011
  · exact classified000100
  · exact classified000101
  · exact classified000110
  · exact classified000111
  · exact classified001000
  · exact classified001001
  · exact classified001010
  · exact classified001011
  · exact classified001100
  · exact classified001101
  · exact classified001110
  · exact classified001111
  · exact classified010000
  · exact classified010001
  · exact classified010010
  · exact classified010011
  · exact classified010100
  · exact classified010101
  · exact classified010110
  · exact classified010111
  · exact classified011000
  · exact classified011001
  · exact classified011010
  · exact classified011011
  · exact classified011100
  · exact classified011101
  · exact classified011110
  · exact classified011111
  · exact classified100000
  · exact classified100001
  · exact classified100010
  · exact classified100011
  · exact classified100100
  · exact classified100101
  · exact classified100110
  · exact classified100111
  · exact classified101000
  · exact classified101001
  · exact classified101010
  · exact classified101011
  · exact classified101100
  · exact classified101101
  · exact classified101110
  · exact classified101111
  · exact classified110000
  · exact classified110001
  · exact classified110010
  · exact classified110011
  · exact classified110100
  · exact classified110101
  · exact classified110110
  · exact classified110111
  · exact classified111000
  · exact classified111001
  · exact classified111010
  · exact classified111011
  · exact classified111100
  · exact classified111101
  · exact classified111110
  · exact classified111111
end QuadraticFourRaw
