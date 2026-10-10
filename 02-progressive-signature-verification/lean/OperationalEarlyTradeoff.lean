import CompletedStoppedInvocation
import CostAndConfidence
import ParameterCertificate

namespace ProgressivePool.OperationalEarlyTradeoff
open MultiEpochExecution StoredCheckExecution OperationalSignatureEndpoint CompletedStoppedInvocation
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F] {r : ℕ}

/-- Initialization-inclusive FIELD-MULTIPLICATION comparison for actual
executions. The seven-row comparator is granted free preprocessing here.
This is not a statement about wall-clock time or all resource dimensions. -/
theorem actual_prefix_below_seven_rows
    (A : Fin 1024 → Fin 61852 → F) (stop : H → Bool)
    (terminal : Phase F H 64 61852 1024 r)
    (phases : List (Phase F H 64 61852 1024 262144))
    (aux : H → Bool) (candidate : H → Input F 61852 1024) (dummy : Fin 1024 → F)
    (u : ℕ) (hr : r+1 ≤ 262144)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F 64 1024)
    (t : ℕ) (indices : Fin t → Fin 64)
    (hN : 262144 ≤ (StoppedSignatureEndpoint.machine A 15463 stop terminal phases
      aux candidate dummy u h draws extra).reservations+1)
    (hS : (StoppedSignatureEndpoint.machine A 15463 stop terminal phases
      aux candidate dummy u h draws extra).trace.length+t ≤
        ((StoppedSignatureEndpoint.machine A 15463 stop terminal phases
          aux candidate dummy u h draws extra).reservations+1)*6) :
    let prior := StoppedSignatureEndpoint.machine A 15463 stop terminal phases
      aux candidate dummy u h draws extra
    let actual := finalMachine A 15463 stop terminal phases aux candidate dummy u h draws extra t indices
    actual.preparationMultiplications + actual.checkingMultiplications <
      (prior.reservations+1)*7*62876 := by
  dsimp only
  rw [finalMachine_total_multiplications A 15463 stop terminal phases aux candidate dummy u hr
    (by norm_num) hFull]
  exact CostAndConfidence.numeric_below_seven_rows _ _ 6 hN hS (le_refl _)

#print axioms actual_prefix_below_seven_rows
end ProgressivePool.OperationalEarlyTradeoff
