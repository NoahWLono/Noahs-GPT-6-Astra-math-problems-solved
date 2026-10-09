import QuadraticFourPairBatch0
import QuadraticFourPairBatch1
import QuadraticFourPairBatch2
import QuadraticFourPairBatch3
import QuadraticFourPairBatch4
import QuadraticFourPairBatch5
import QuadraticFourPairBatch6
import QuadraticFourPairBatch7
namespace QuadraticFourRaw
theorem all_pairs : ∀ f g h i j k F G H I J K : QuadraticFourRaw.F,
    pairProperty f g h i j k F G H I J K := by
  intro f g h i j k
  fin_cases f <;> fin_cases g <;> fin_cases h <;> fin_cases i <;> fin_cases j <;> fin_cases k
  · exact pair000000
  · exact pair000001
  · exact pair000010
  · exact pair000011
  · exact pair000100
  · exact pair000101
  · exact pair000110
  · exact pair000111
  · exact pair001000
  · exact pair001001
  · exact pair001010
  · exact pair001011
  · exact pair001100
  · exact pair001101
  · exact pair001110
  · exact pair001111
  · exact pair010000
  · exact pair010001
  · exact pair010010
  · exact pair010011
  · exact pair010100
  · exact pair010101
  · exact pair010110
  · exact pair010111
  · exact pair011000
  · exact pair011001
  · exact pair011010
  · exact pair011011
  · exact pair011100
  · exact pair011101
  · exact pair011110
  · exact pair011111
  · exact pair100000
  · exact pair100001
  · exact pair100010
  · exact pair100011
  · exact pair100100
  · exact pair100101
  · exact pair100110
  · exact pair100111
  · exact pair101000
  · exact pair101001
  · exact pair101010
  · exact pair101011
  · exact pair101100
  · exact pair101101
  · exact pair101110
  · exact pair101111
  · exact pair110000
  · exact pair110001
  · exact pair110010
  · exact pair110011
  · exact pair110100
  · exact pair110101
  · exact pair110110
  · exact pair110111
  · exact pair111000
  · exact pair111001
  · exact pair111010
  · exact pair111011
  · exact pair111100
  · exact pair111101
  · exact pair111110
  · exact pair111111
end QuadraticFourRaw
