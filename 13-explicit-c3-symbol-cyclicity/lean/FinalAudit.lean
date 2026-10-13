module
public import FinalAssembly
@[expose] public section
set_option pp.universes true
set_option pp.proofs false
#print PrimeFiveFamily.SymbolFamily
#print PrimeFiveFamily.FixedScalars
#print PrimeFiveFamily.FixedAlgebra
#print C3BasisDescent.fixedField
#print C3BasisDescent.fixedAlgebra
#print PrimeFiveFamily.frozenNumerator
#print PrimeFiveFamily.fixedNumerator
#print PrimeFiveFamily.fifthScalar
#print PrimeCyclicityEndpoint.Generated
#check @PrimeFiveFamily.fifthOutput_eq_candidate
#check @PrimeFiveFamily.frozenNumerator_fifth
#check @PrimeFiveFamily.symbolFamily_cyclicity
#print PrimeFiveFamily.symbolFamily_cyclicity
#print axioms PrimeFiveFamily.fifthOutput_eq_candidate
#print axioms PrimeFiveFamily.fifthScalar
#print axioms PrimeFiveFamily.frozenNumerator_fifth
#print axioms PrimeFiveFamily.symbolFamily_cyclicity
#print axioms PrimeCyclicity.N5Modern.numerator_fifth
#print axioms FrozenCentralOutput75.candidateOutput75_support
#print axioms ConcreteCoordinateBridge.evalLaurent_scalar_of_support
#print axioms PrimeFiveFamily.supporting_cyclicity_of_fifthPower_identity
