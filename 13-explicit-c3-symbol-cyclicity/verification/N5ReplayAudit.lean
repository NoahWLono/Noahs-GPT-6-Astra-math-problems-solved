module
import modern.N5Fifth
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
#print axioms PrimeCyclicity.N5Modern.processed69_eq_numerator
#print axioms PrimeCyclicity.N5Modern.numerator_fifth
#check @PrimeCyclicity.N5Modern.numerator_fifth
example : PrimeCyclicity.N5Modern.acc69.length = 75 := by decide +kernel
