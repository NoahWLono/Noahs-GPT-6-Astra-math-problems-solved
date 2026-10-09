import MaskLists
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12
theorem membership06 : ∀ x : BitVec 8, ((embed 6 x ≠ 0 ∧ (embed 6 x).setWidth 8 ∈ effectiveNonbent) ↔ embed 6 x ∈ nonbentMasks) := by decide
end N12
