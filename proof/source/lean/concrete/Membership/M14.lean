import MaskLists
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12
theorem membership14 : ∀ x : BitVec 8, ((embed 14 x ≠ 0 ∧ (embed 14 x).setWidth 8 ∈ effectiveNonbent) ↔ embed 14 x ∈ nonbentMasks) := by decide
end N12
