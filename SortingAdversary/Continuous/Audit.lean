import SortingAdversary.Continuous.Accounting
import SortingAdversary.Continuous.Admission
import SortingAdversary.Continuous.ApproximateCounting
import SortingAdversary.Continuous.ArbitraryLabelProofs
import SortingAdversary.Continuous.ArbitraryLabels
import SortingAdversary.Continuous.ArcBudget
import SortingAdversary.Continuous.CentralQuantiles
import SortingAdversary.Continuous.CertificateProbability
import SortingAdversary.Continuous.CertificateSuccess
import SortingAdversary.Continuous.CertificateWork
import SortingAdversary.Continuous.Certificates
import SortingAdversary.Continuous.ComparableBound
import SortingAdversary.Continuous.ComparableDensity
import SortingAdversary.Continuous.ComponentSwap
import SortingAdversary.Continuous.ConcreteRoutines
import SortingAdversary.Continuous.Conditioning
import SortingAdversary.Continuous.Controller
import SortingAdversary.Continuous.ControllerAsymptotics
import SortingAdversary.Continuous.ControllerBounds
import SortingAdversary.Continuous.ControllerConsequences
import SortingAdversary.Continuous.ControllerCorrect
import SortingAdversary.Continuous.ControllerInvariant
import SortingAdversary.Continuous.ControllerLegality
import SortingAdversary.Continuous.ControllerLocal
import SortingAdversary.Continuous.ControllerPrecision
import SortingAdversary.Continuous.ControllerRepair
import SortingAdversary.Continuous.ControllerResources
import SortingAdversary.Continuous.ControllerSelection
import SortingAdversary.Continuous.ControllerSemantics
import SortingAdversary.Continuous.ControllerSupport
import SortingAdversary.Continuous.ControllerWork
import SortingAdversary.Continuous.ControllerWorkBounds
import SortingAdversary.Continuous.Counting
import SortingAdversary.Continuous.Density
import SortingAdversary.Continuous.DensityCertificates
import SortingAdversary.Continuous.Dyadic
import SortingAdversary.Continuous.EnclosureCoupling
import SortingAdversary.Continuous.EnclosureDistribution
import SortingAdversary.Continuous.EnclosureGuarantee
import SortingAdversary.Continuous.EnclosureParameters
import SortingAdversary.Continuous.EnclosureWork
import SortingAdversary.Continuous.Examples
import SortingAdversary.Continuous.FeasibleRank
import SortingAdversary.Continuous.FiniteAveraging
import SortingAdversary.Continuous.FiniteDependence
import SortingAdversary.Continuous.FiniteTreeLaw
import SortingAdversary.Continuous.GraphOrder
import SortingAdversary.Continuous.GraphPaths
import SortingAdversary.Continuous.GraphScanWork
import SortingAdversary.Continuous.GraphWork
import SortingAdversary.Continuous.InducedEnclosure
import SortingAdversary.Continuous.LayerAdversary
import SortingAdversary.Continuous.LayerReduction
import SortingAdversary.Continuous.LocalEnclosure
import SortingAdversary.Continuous.LocalSelection
import SortingAdversary.Continuous.LocalSelectionProofs
import SortingAdversary.Continuous.MachineWork
import SortingAdversary.Continuous.MarginalMeasure
import SortingAdversary.Continuous.Neighborhood
import SortingAdversary.Continuous.NeighborhoodCertificates
import SortingAdversary.Continuous.NeighborhoodWork
import SortingAdversary.Continuous.Normalization
import SortingAdversary.Continuous.OneArcRepair
import SortingAdversary.Continuous.OperandBounds
import SortingAdversary.Continuous.OrderRegion
import SortingAdversary.Continuous.Packing
import SortingAdversary.Continuous.ParameterBounds
import SortingAdversary.Continuous.Precision
import SortingAdversary.Continuous.ProjectionDensity
import SortingAdversary.Continuous.QueriedCompression
import SortingAdversary.Continuous.Rates
import SortingAdversary.Continuous.RationalSemantics
import SortingAdversary.Continuous.RationalState
import SortingAdversary.Continuous.RecordInvariant
import SortingAdversary.Continuous.RefinementBatch
import SortingAdversary.Continuous.RegionMeasure
import SortingAdversary.Continuous.Reindex
import SortingAdversary.Continuous.RoundingWork
import SortingAdversary.Continuous.RuntimeOperands
import SortingAdversary.Continuous.RuntimePrecision
import SortingAdversary.Continuous.Sampling
import SortingAdversary.Continuous.ScalarTariffs
import SortingAdversary.Continuous.SectionConcavity
import SortingAdversary.Continuous.SelectionKernelWork
import SortingAdversary.Continuous.SelectionTermination
import SortingAdversary.Continuous.SelectionWork
import SortingAdversary.Continuous.SmallDifference
import SortingAdversary.Continuous.StageArithmetic
import SortingAdversary.Continuous.StageWork
import SortingAdversary.Continuous.StateInvariants
import SortingAdversary.Continuous.StateOperandBounds
import SortingAdversary.Continuous.StateWork
import SortingAdversary.Continuous.Stationarity
import SortingAdversary.Continuous.TraceAccounting
import SortingAdversary.Continuous.TraceGuarantees
import SortingAdversary.Continuous.TreePacking
import SortingAdversary.Continuous.TreeRouting
import SortingAdversary.Continuous.TreeSampling
import SortingAdversary.Continuous.TreeState
import SortingAdversary.Continuous.TreeVolume
import SortingAdversary.Continuous.UniformAdversary
import SortingAdversary.Continuous.UniformEfficient
import SortingAdversary.Continuous.UniformInitializationWork
import SortingAdversary.Continuous.UniformMachineWork
import SortingAdversary.Continuous.UniformStages
import SortingAdversary.Continuous.Weights

import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Enforced axiom audit for the continuous construction

Every declaration owned by an imported `SortingAdversary.Continuous.*`
module is checked, including private declarations, generated auxiliaries and
names declared outside the namespace. The gate collects transitive axiom
dependencies and rejects everything except `propext`, `Classical.choice` and
`Quot.sound`. In particular, a native evaluator assumption is not permitted.

This is a proof trust check. Exact correspondence with the manuscript and
with the measured program is established by the theorems in the imported
modules, rather than by the audit command itself.
-/

open Lean Elab Command in
elab "#audit_continuous_axioms" : command => do
  let env ← getEnv
  let auditedNamespace := `SortingAdversary.Continuous
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut failures : Array (Name × Name) := #[]
  for (declName, _) in env.constants.toList do
    let userName := (privateToUserName? declName).getD declName
    let byNamespace := auditedNamespace.isPrefixOf userName
    let byModule := match env.getModuleIdxFor? declName with
      | none => false
      | some idx =>
        let moduleName := env.header.moduleNames[idx.toNat]!
        moduleName != `SortingAdversary.Continuous.Audit && auditedNamespace.isPrefixOf moduleName
    if byNamespace || byModule then
      checked := checked + 1
      for axiomName in ← collectAxioms declName do
        unless allowed.contains axiomName do
          failures := failures.push (declName, axiomName)
  unless failures.isEmpty do
    for (declName, axiomName) in failures do
      logError m!"Continuous axiom audit rejected {declName}: forbidden dependency {axiomName}"
    throwError "Continuous axiom audit failed: {failures.size} forbidden axiom dependencies"
  if checked == 0 then
    throwError "Continuous axiom audit checked no declarations; proof imports are missing"
  logInfo m!"Continuous axiom audit passed: {checked} declarations; only propext, Classical.choice, Quot.sound allowed"

#print axioms SortingAdversary.Continuous.Controller.compareGuarantee
#print axioms SortingAdversary.Continuous.Controller.prefix_count
#print axioms SortingAdversary.Continuous.UniformAdversary.consistent
#print axioms SortingAdversary.Continuous.UniformAdversary.asymptoticallyOptimal
#print axioms SortingAdversary.Continuous.UniformAdversary.worst_case
#print axioms SortingAdversary.Continuous.UniformAdversary.production

#print axioms SortingAdversary.Continuous.UniformMachineWork.strategy_eq
#print axioms SortingAdversary.Continuous.UniformMachineWork.per_query_polynomial
#print axioms SortingAdversary.Continuous.UniformEfficient.asymptoticallyOptimal_and_polynomial

#audit_continuous_axioms
