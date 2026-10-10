import MultiEpochExecution

namespace ProgressivePool.OperationalSignatureEndpoint
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation
set_option maxHeartbeats 1000000
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}

def phaseSource (A : Fin n → Fin m → F) (p : Phase F H s m n r) :
    SignatureEpoch s H F (Fin n) H where
  query h := flattenInvocations (mapInvocationInputs A (p h))
  next h C := runOutput C (flattenInvocations (mapInvocationInputs A (p h)))
  invoke _ _ := true

def sources (A : Fin n → Fin m → F) (terminal : Phase F H s m n r) :
    List (Phase F H s m n R) → List (SignatureEpoch s H F (Fin n) H)
  | [] => [phaseSource A terminal]
  | p::ps => phaseSource A p :: sources A terminal ps

abbrev residual (A : Fin n → Fin m → F) (candidate : H → Input F m n) (h : H) :=
  mvResidual A (candidate h).1 (candidate h).2

noncomputable def compiled (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (phases : List (Phase F H s m n R)) (aux : H → Bool)
    (candidate : H → Input F m n) (dummy : Fin n → F) :=
  (sources A terminal phases).map
    (fun e => compileSignatureEpoch e aux (residual A candidate) dummy)

abbrev Draws (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (phases : List (Phase F H s m n R)) (aux : H → Bool)
    (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ) :=
  Samples (Bank F s n) ((compiled A terminal phases aux candidate dummy).map
    (fun e => e.toEpoch u)).length

/-- Append one independent bank for the final unused prefetch. The active-bank
sample law is unchanged; the resulting visible output is proved independent
of this extra bank. -/
noncomputable def pack (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ) :
    (phases : List (Phase F H s m n R)) →
    Draws A terminal phases aux candidate dummy u → Bank F s n →
    Samples (Bank F s n) (phases.length+2)
  | [], draws, extra => (draws.1, (extra, PUnit.unit))
  | _::ps, draws, extra => (draws.1, pack A terminal aux candidate dummy u ps draws.2 extra)

noncomputable def rawFinal (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ) :
    (phases : List (Phase F H s m n R)) → H →
    Draws A terminal phases aux candidate dummy u → H × Bank F s n
  | [], h, draws => ((phaseSource A terminal).next h draws.1, draws.1)
  | p::ps, h, draws => rawFinal A terminal aux candidate dummy u ps
      ((phaseSource A p).next h draws.1) draws.2

theorem rawRun_pack (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (phases : List (Phase F H s m n R)) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :
    let packed := pack A terminal aux candidate dummy u phases draws extra
    rawRun A terminal phases h packed.1 packed.2 =
      rawFinal A terminal aux candidate dummy u phases h draws := by
  induction phases generalizing h with
  | nil => rfl
  | cons p ps ih => exact ih ((phaseSource A p).next h draws.1) draws.2

noncomputable def machine (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :=
  coldRun A W terminal phases h (pack A terminal aux candidate dummy u phases draws extra)

theorem machine_refines (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, Full A p) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :
    let actual := machine A W terminal phases aux candidate dummy u h draws extra
    let spec := rawFinal A terminal aux candidate dummy u phases h draws
    actual.output = spec.1 ∧ actual.current = spec.2 ∧
      Ready A actual.current actual.prepared := by
  have hh := coldRun_refines A W terminal phases hB hFull h
    (pack A terminal aux candidate dummy u phases draws extra)
  rw [rawRun_pack] at hh
  exact hh

def errorGate (A : Fin n → Fin m → F) (aux : H → Bool)
    (candidate : H → Input F m n) (h : H) : Bool :=
  aux h && decide (residual A candidate h ≠ 0)

theorem source_active (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (phases : List (Phase F H s m n R)) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) :
    activeAt u (compiled A terminal phases aux candidate dummy) h draws phases.length =
      errorGate A aux candidate (rawFinal A terminal aux candidate dummy u phases h draws).1 := by
  induction phases generalizing h with
  | nil => rfl
  | cons p ps ih => exact ih ((phaseSource A p).next h draws.1) draws.2

theorem source_zeros (A : Fin n → Fin m → F) (terminal : Phase F H s m n r)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (phases : List (Phase F H s m n R)) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) :
    let spec := rawFinal A terminal aux candidate dummy u phases h draws
    zeroRowsAt u (compiled A terminal phases aux candidate dummy) h draws phases.length =
      if errorGate A aux candidate spec.1 then
        univ.filter (fun j => rowDot (residual A candidate spec.1) (spec.2 j) = 0) else ∅ := by
  induction phases generalizing h with
  | nil =>
      by_cases hz : residual A candidate ((phaseSource A terminal).next h draws.1) = 0
      · simp only [phaseSource] at hz
        simp [compiled,sources,zeroRowsAt,compileSignatureEpoch,rawFinal,phaseSource,
          errorGate,finalZeroRows,runOutput_map,hz]
      · simp only [phaseSource] at hz
        simp [compiled,sources,zeroRowsAt,compileSignatureEpoch,rawFinal,phaseSource,
          errorGate,finalZeroRows,runOutput_map,hz]
  | cons p ps ih => exact ih ((phaseSource A p).next h draws.1) draws.2

noncomputable def storedZeros (Z : Prepared F s m) (C : Bank F s n)
    (input : Input F m n) : Finset (Fin s) :=
  univ.filter (fun j => (evalStored Z C j input).value = 0)

/-- Actual stored final-check zero set, after all operational promotions. -/
theorem machine_zeros (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, Full A p) (h : H)
    (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n) :
    let actual := machine A W terminal phases aux candidate dummy u h draws extra
    let spec := rawFinal A terminal aux candidate dummy u phases h draws
    storedZeros actual.prepared actual.current (candidate actual.output) =
      univ.filter (fun j => rowDot (residual A candidate spec.1) (spec.2 j) = 0) := by
  have hh := machine_refines A W terminal phases aux candidate dummy u hB hFull h draws extra
  dsimp only
  ext j
  simp only [storedZeros,mem_filter,mem_univ,true_and]
  rw [stored_value_correct A _ _ hh.2.2, hh.1, hh.2.1]

/-- Exact invalid-acceptance mass of the implemented initialized machine,
using its actual active stored matrix. T is fixed before its fresh final
indices. A separate extra bank permits arbitrary unused final prefetch. -/
noncomputable def machineErrorMass (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) : ℚ :=
  FreshSampling.acceptMass univ
    (fun draws => let actual := machine A W terminal phases aux candidate dummy u h draws extra
      if errorGate A aux candidate actual.output then
        sampleWeight ((compiled A terminal phases aux candidate dummy).map
          (fun e => e.toEpoch u)).length draws else 0)
    (fun draws => let actual := machine A W terminal phases aux candidate dummy u h draws extra
      storedZeros actual.prepared actual.current (candidate actual.output)) T

/-- The entire operational error experiment is the already bounded mixed-output
signature experiment. This is equality, including Aux rejection and T=0. -/
theorem machine_mass_eq (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, Full A p) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    machineErrorMass A W terminal phases aux candidate dummy u h extra T =
      gatedEpochErrorMass (compiled A terminal phases aux candidate dummy) u h
        (fun _ => phases.length) T := by
  rw [machineErrorMass,gatedEpochErrorMass,FreshSampling.acceptMass_eq,FreshSampling.acceptMass_eq]
  apply sum_congr rfl
  intro draws hd
  have hh := machine_refines A W terminal phases aux candidate dummy u hB hFull h draws extra
  have hz := machine_zeros A W terminal phases aux candidate dummy u hB hFull h draws extra
  dsimp only
  rw [hz,hh.1,source_active,source_zeros]
  split_ifs <;> simp

@[simp] theorem sources_length (A : Fin n → Fin m → F)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R)) :
    (sources A terminal phases).length = phases.length+1 := by
  induction phases with
  | nil => rfl
  | cons p ps ih => simp [sources,ih,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem sources_depth (A : Fin n → Fin m → F)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (k : ℕ) (hr : r ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h))) :
    ∀ e ∈ sources A terminal phases, ∀ h, queryHeight (e.query h) ≤ R*k := by
  induction phases with
  | nil =>
      intro e he h
      have he' : e = phaseSource A terminal := by simpa [sources] using he
      subst e
      exact (reserved_query_budget _ (ht h)).trans (Nat.mul_le_mul_right k hr)
  | cons p ps ih =>
      intro e he h
      rcases List.mem_cons.mp he with he|he
      · subst e
        exact reserved_query_budget _ (hc p (by simp) h)
      · exact ih (fun p hp => hc p (by simp [hp])) e he h

/-- Initialization-inclusive operational compiler security. The game is the
actual stored checker after actual cursor preparation and buffer promotion.
The remaining signature assumption is only the separately supplied ordinary
signature security term; this theorem bounds additional invalid acceptance. -/
theorem operational_signature_bound (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, Full A p) (hr : r ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h)))
    (hfield : R*k+s < Fintype.card F) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    machineErrorMass A W terminal phases aux candidate dummy u h extra T ≤
      (∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
        (fun e => e.toEpoch u)).length draws * (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u) := by
  rw [machine_mass_eq A W terminal phases aux candidate dummy u hB hFull]
  have hh := global_signature_verification_error hs (sources A terminal phases) aux
    (residual A candidate) dummy hdummy (R*k) u hu
    (sources_depth A terminal phases k hr hc ht) hfield h (fun _ => phases.length) T
  simpa only [compiled,sources_length] using hh

#print axioms machine_refines
#print axioms source_active
#print axioms source_zeros
#print axioms machine_zeros
#print axioms machine_mass_eq
#print axioms operational_signature_bound
end ProgressivePool.OperationalSignatureEndpoint
