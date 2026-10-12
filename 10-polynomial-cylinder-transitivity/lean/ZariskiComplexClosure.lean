module
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section
namespace ZariskiCylinder
/-- Direct use of the pinned official Mathlib fundamental theorem of algebra. -/
theorem complexIsAlgClosed : IsAlgClosed ℂ := inferInstance
#print axioms complexIsAlgClosed
end ZariskiCylinder
