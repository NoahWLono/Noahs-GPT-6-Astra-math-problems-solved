import StoppingEpochExecution
import GlobalSignatureJoint
import FinalStoredInvocation

namespace ProgressivePool.StoppedSignatureEndpoint
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint
set_option maxHeartbeats 1200000
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}

/-- Adversarial first-stop selector is fixed before any final fresh index. -/
noncomputable def rawFinal (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (aux : H → Bool)
    (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ) :
    (phases : List (Phase F H s m n R)) → H →
    Draws A terminal phases aux candidate dummy u → StoppingEpochExecution.RawResult F H s n
  | [], h, draws => ⟨(phaseSource A terminal).next h draws.1, draws.1, 0,
      (invocationDepths draws.1 (mapInvocationInputs A (terminal h))).length⟩
  | p::ps, h, draws =>
      let out := (phaseSource A p).next h draws.1
      if stop out then ⟨out, draws.1, 0,
        (invocationDepths draws.1 (mapInvocationInputs A (p h))).length⟩
      else let rest := rawFinal A stop terminal aux candidate dummy u ps out draws.2
        { rest with selectedEpoch := rest.selectedEpoch+1 }

theorem rawRun_pack (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (aux : H → Bool)
    (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (phases : List (Phase F H s m n R)) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :
    let packed := pack A terminal aux candidate dummy u phases draws extra
    StoppingEpochExecution.rawRun A stop terminal phases h packed.1 packed.2 =
      rawFinal A stop terminal aux candidate dummy u phases h draws := by
  induction phases generalizing h with
  | nil => rfl
  | cons p ps ih =>
      simp only [pack,StoppingEpochExecution.rawRun,rawFinal,phaseSource]
      split
      · rfl
      · rw [ih]

noncomputable def machine (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :=
  StoppingEpochExecution.coldRun A W stop terminal phases h
    (pack A terminal aux candidate dummy u phases draws extra)

theorem machine_refines (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :
    let actual := machine A W stop terminal phases aux candidate dummy u h draws extra
    let spec := rawFinal A stop terminal aux candidate dummy u phases h draws
    actual.output = spec.output ∧ actual.current = spec.current ∧
      actual.selectedEpoch = spec.selectedEpoch ∧ actual.localReservations = spec.localReservations ∧
      Ready A actual.current actual.prepared := by
  have hh := StoppingEpochExecution.coldRun_refines A W stop terminal phases hB hFull h
    (pack A terminal aux candidate dummy u phases draws extra)
  rw [rawRun_pack] at hh
  exact hh

theorem source_active (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (aux : H → Bool)
    (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (phases : List (Phase F H s m n R)) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) :
    let spec := rawFinal A stop terminal aux candidate dummy u phases h draws
    activeAt u (compiled A terminal phases aux candidate dummy) h draws spec.selectedEpoch =
      errorGate A aux candidate spec.output := by
  induction phases generalizing h with
  | nil => rfl
  | cons p ps ih =>
      simp only [rawFinal]
      split
      · rfl
      · exact ih ((phaseSource A p).next h draws.1) draws.2

theorem source_zeros (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (aux : H → Bool)
    (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (phases : List (Phase F H s m n R)) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) :
    let spec := rawFinal A stop terminal aux candidate dummy u phases h draws
    zeroRowsAt u (compiled A terminal phases aux candidate dummy) h draws spec.selectedEpoch =
      if errorGate A aux candidate spec.output then
        univ.filter (fun j => rowDot (residual A candidate spec.output) (spec.current j) = 0) else ∅ := by
  induction phases generalizing h with
  | nil => exact OperationalSignatureEndpoint.source_zeros A terminal aux candidate dummy u [] h draws
  | cons p ps ih =>
      simp only [rawFinal]
      split
      · exact OperationalSignatureEndpoint.source_zeros (R := R) A p aux candidate dummy u [] h (draws.1,PUnit.unit)
      · exact ih ((phaseSource A p).next h draws.1) draws.2

theorem machine_zeros (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :
    let actual := machine A W stop terminal phases aux candidate dummy u h draws extra
    let spec := rawFinal A stop terminal aux candidate dummy u phases h draws
    storedZeros actual.prepared actual.current (candidate actual.output) =
      univ.filter (fun j => rowDot (residual A candidate spec.output) (spec.current j) = 0) := by
  have hh := machine_refines A W stop terminal phases aux candidate dummy u hB hFull h draws extra
  dsimp only
  ext j
  simp only [storedZeros,mem_filter,mem_univ,true_and]
  rw [stored_value_correct A _ _ hh.2.2.2.2, hh.1, hh.2.1]

/-- Event-restricted actual invalid acceptance. The final indices are newly
uniform after this entire stopped machine fixes the candidate and threshold. -/
noncomputable def machineErrorMass (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (extra : Bank F s n)
    (event : Draws A terminal phases aux candidate dummy u → Bool)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) : ℚ :=
  FreshSampling.acceptMass univ
    (fun draws => let actual := machine A W stop terminal phases aux candidate dummy u h draws extra
      if errorGate A aux candidate actual.output && event draws then
        sampleWeight ((compiled A terminal phases aux candidate dummy).map
          (fun e => e.toEpoch u)).length draws else 0)
    (fun draws => let actual := machine A W stop terminal phases aux candidate dummy u h draws extra
      storedZeros actual.prepared actual.current (candidate actual.output)) T

theorem machine_mass_eq (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (h : H) (extra : Bank F s n)
    (event : Draws A terminal phases aux candidate dummy u → Bool)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    let select := fun draws => (rawFinal A stop terminal aux candidate dummy u phases h draws).selectedEpoch
    machineErrorMass A W stop terminal phases aux candidate dummy u h extra event T =
      FreshSampling.acceptMass univ
        (fun draws => if activeAt u (compiled A terminal phases aux candidate dummy) h draws
          (select draws) && event draws then sampleWeight ((compiled A terminal phases aux candidate dummy).map
            (fun e => e.toEpoch u)).length draws else 0)
        (fun draws => zeroRowsAt u (compiled A terminal phases aux candidate dummy) h draws (select draws)) T := by
  dsimp only
  rw [machineErrorMass,FreshSampling.acceptMass_eq,FreshSampling.acceptMass_eq]
  apply sum_congr rfl
  intro draws hd
  have hh := machine_refines A W stop terminal phases aux candidate dummy u hB hFull h draws extra
  have hz := machine_zeros A W stop terminal phases aux candidate dummy u hB hFull h draws extra
  dsimp only
  rw [hz,hh.1,source_active,source_zeros]
  by_cases hg : errorGate A aux candidate
      (rawFinal A stop terminal aux candidate dummy u phases h draws).output = true
  · simp [hg]
  · simp [hg]

/-- Full bounded adaptive-stopping operational compiler endpoint. Aux failure,
zero residuals, zero threshold, earlier stopping and unused prefetch all retain
their actual event semantics. This is additional verification error only. -/
theorem operational_signature_bound (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (hr : r ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h)))
    (hfield : R*k+s < Fintype.card F) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    machineErrorMass A W stop terminal phases aux candidate dummy u h extra (fun _ => true) T ≤
      (∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
        (fun e => e.toEpoch u)).length draws * (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u) := by
  rw [machine_mass_eq A W stop terminal phases aux candidate dummy u hB hFull]
  have hh := global_signature_verification_error hs (sources A terminal phases) aux
    (residual A candidate) dummy hdummy (R*k) u hu
    (sources_depth A terminal phases k hr hc ht) hfield h
    (fun draws => (rawFinal A stop terminal aux candidate dummy u phases h draws).selectedEpoch) T
  simpa only [compiled,sources_length,gatedEpochErrorMass,Bool.and_true] using hh

theorem operational_signature_joint (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (hr : r ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h)))
    (hfield : R*k+s < Fintype.card F) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) (t : ℕ) :
    machineErrorMass A W stop terminal phases aux candidate dummy u h extra
      (fun draws => decide (T draws = t)) T ≤
      (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
        (∑ draws ∈ univ.filter (fun draws => T draws = t),
          sampleWeight ((compiled A terminal phases aux candidate dummy).map
            (fun e => e.toEpoch u)).length draws) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u) := by
  rw [machine_mass_eq A W stop terminal phases aux candidate dummy u hB hFull]
  have hh := global_signature_joint hs (sources A terminal phases) aux
    (residual A candidate) dummy hdummy (R*k) u hu
    (sources_depth A terminal phases k hr hc ht) hfield h
    (fun draws => (rawFinal A stop terminal aux candidate dummy u phases h draws).selectedEpoch) T t
  simpa only [compiled,sources_length,gatedEpochJointMass] using hh

#print axioms machine_refines
#print axioms source_active
#print axioms source_zeros
#print axioms machine_zeros
#print axioms machine_mass_eq
#print axioms operational_signature_bound
#print axioms operational_signature_joint
end ProgressivePool.StoppedSignatureEndpoint
