import UniformRow
import RowExclusions
import AdaptiveTranscript
import FirstSpoilCounting
import FieldTranscript
import ProductCells
import ActualConditionalBound
import HistoryCells
import AdaptiveTail
import ConcreteAdaptiveTail
import SpoiledRows
import FinalResidual
import FreshSampling
import FreshSamplingJoint
import UniformPoolEndpoint
import EpochComposition
import EpochPrefix
import ConcreteEpochs
import EpochFreshEndpoint
import EpochFreshJoint
import StoredRows
import SignatureCompiler
import BaseSecurityTerm
import GlobalSignatureCompiler
import CostAndConfidence
import InvocationBudget
import IncrementalPreparation
import IndexedPreparation
import BufferedExecution
import OperationalCost
import CursorBufferedExecution
import ParameterCertificate
import StoredCheckExecution
import StoredBufferedExecution
import MultiEpochExecution
import MultiEpochCost
import OperationalSignatureEndpoint
import StoppingEpochExecution
import TraceErasure
import GlobalSignatureJoint
import FinalStoredInvocation
import StoppedSignatureEndpoint
import CompletedStoppedInvocation
import RandomTapeAveraging
import RandomizedStoppedEndpoint
import PrimeDivisorBlocks0
import PrimeDivisorBlocks1
import PrimeDivisorBlocks2
import PrimeDivisorBlocks3
import PrimeDivisorBlocks4
import PrimeDivisorBlocks5
import PrimeDivisorBlocks6
import PrimeDivisorBlocks7
import PrimeCertificate
import CertifiedField
import CertifiedParameters
import FiniteForgerySplit
import StoppedForgerySplit
import VerifiedCompiler
import FinalTraceErasure
import VerifierInterface
import RandomizedFinalJoint
import StoppedSourceBound
import EpochResourceBounds
import OperationalEarlyTradeoff
import MatchedEarlyCertificates
import CompilerBundle
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let moduleNames : List Name := [`UniformRow, `RowExclusions, `AdaptiveTranscript, `FirstSpoilCounting, `FieldTranscript, `ProductCells, `ActualConditionalBound, `HistoryCells, `AdaptiveTail, `ConcreteAdaptiveTail, `SpoiledRows, `FinalResidual, `FreshSampling, `FreshSamplingJoint, `UniformPoolEndpoint, `EpochComposition, `EpochPrefix, `ConcreteEpochs, `EpochFreshEndpoint, `EpochFreshJoint, `StoredRows, `SignatureCompiler, `BaseSecurityTerm, `GlobalSignatureCompiler, `CostAndConfidence, `InvocationBudget, `IncrementalPreparation, `IndexedPreparation, `BufferedExecution, `OperationalCost, `CursorBufferedExecution, `ParameterCertificate, `StoredCheckExecution, `StoredBufferedExecution, `MultiEpochExecution, `MultiEpochCost, `OperationalSignatureEndpoint, `StoppingEpochExecution, `TraceErasure, `GlobalSignatureJoint, `FinalStoredInvocation, `StoppedSignatureEndpoint, `CompletedStoppedInvocation, `RandomTapeAveraging, `RandomizedStoppedEndpoint, `PrimeDivisorBlocks0, `PrimeDivisorBlocks1, `PrimeDivisorBlocks2, `PrimeDivisorBlocks3, `PrimeDivisorBlocks4, `PrimeDivisorBlocks5, `PrimeDivisorBlocks6, `PrimeDivisorBlocks7, `PrimeCertificate, `CertifiedField, `CertifiedParameters, `FiniteForgerySplit, `StoppedForgerySplit, `VerifiedCompiler, `FinalTraceErasure, `VerifierInterface, `RandomizedFinalJoint, `StoppedSourceBound, `EpochResourceBounds, `OperationalEarlyTradeoff, `MatchedEarlyCertificates, `CompilerBundle]
  let moduleIds := moduleNames.filterMap env.getModuleIdx?
  unless moduleIds.length == 67 do throwError "Missing imported manifest modules"
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).any (fun idx => moduleIds.contains idx) && info.isTheorem then
      let axs ← collectAxioms name
      logInfo m!"AUDIT {name} : {axs}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError m!"NONSTANDARD_AXIOM {name}: {ax}"
      if info.isTheorem then count := count + 1
  logInfo m!"AUDIT_THEOREM_COUNT={count}"
