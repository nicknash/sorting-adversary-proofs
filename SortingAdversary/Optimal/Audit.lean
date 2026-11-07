import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.LocalChoice
import SortingAdversary.Optimal.Routing
import SortingAdversary.Optimal.Refinement
import SortingAdversary.Optimal.FiniteRefinement
import SortingAdversary.Optimal.Insertion
import SortingAdversary.Optimal.Terminal
import SortingAdversary.Optimal.Accounting
import SortingAdversary.Optimal.GroupEntropy
import SortingAdversary.Optimal.Parameters
import SortingAdversary.Optimal.Endpoints
import SortingAdversary.Optimal.ComparisonBound
import SortingAdversary.Optimal.Examples
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Enforced axiom audit for the recursive-adversary formalization

`#audit_optimal_axioms` checks every declaration in the
`SortingAdversary.Optimal` namespace, including private declarations and
generated auxiliary declarations. It also checks declarations belonging to
imported `SortingAdversary.Optimal.*` proof modules even if they were declared
outside that namespace.

For each declaration Lean collects **all transitive axiom dependencies**. The
only allowed axioms are the standard foundations `propext`, `Classical.choice`,
and `Quot.sound`. Placeholder proofs, native evaluation assumptions, and custom
axioms cause a hard elaboration error; simply printing an axiom list is not the
gate. The command can be rerun after additional declarations in a downstream
file, which also permits testing the gate against intentionally bad probes.

The audit implementation itself is metaprogramming, not an additional theorem.
Its module is excluded from module-ownership selection; mathematical names in
the audited namespace are still checked even if introduced here. Every proof
module must be imported above so its declarations enter this environment.

Passing this gate establishes a proof trust boundary, not the completeness of
the manuscript formalization. In particular,
`comparison_guarantee_of_vanishing_accounting` still has explicit controller
legality and accounting hypotheses, and asserts no polynomial running time.
-/

open Lean Elab Command in
/-- Reject any nonstandard axiom used anywhere in the imported optimal
formalization, including declarations not reached by a chosen headline theorem. -/
elab "#audit_optimal_axioms" : command => do
  let env ← getEnv
  let auditedNamespace := `SortingAdversary.Optimal
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
        moduleName != `SortingAdversary.Optimal.Audit && auditedNamespace.isPrefixOf moduleName
    if byNamespace || byModule then
      checked := checked + 1
      for axiomName in ← collectAxioms declName do
        unless allowed.contains axiomName do
          failures := failures.push (declName, axiomName)
  unless failures.isEmpty do
    for (declName, axiomName) in failures do
      logError m!"Optimal axiom audit rejected {declName}: forbidden dependency {axiomName}"
    throwError "Optimal axiom audit failed: {failures.size} forbidden axiom dependencies"
  if checked == 0 then
    throwError "Optimal axiom audit checked no declarations; proof imports are missing"
  logInfo m!"Optimal axiom audit passed: {checked} declarations; only propext, Classical.choice, Quot.sound allowed"

-- Human-readable anchor points complement the enforced all-declaration gate.
#print axioms SortingAdversary.Optimal.WeakMaps.WeakSystem.branch_count_identity
#print axioms SortingAdversary.Optimal.Routing.both_inner_witnesses_delegate
#print axioms SortingAdversary.Optimal.Refinement.liftMap_respects
#print axioms SortingAdversary.Optimal.FiniteRefinement.lower_refinement_count
#print axioms SortingAdversary.Optimal.FiniteRefinement.upper_refinement_count
#print axioms SortingAdversary.Optimal.Insertion.width_mul_deleted_count_le_twice_full
#print axioms SortingAdversary.Optimal.Insertion.near_count_mul_width_le
#print axioms SortingAdversary.Optimal.Terminal.card_monotoneColorMap
#print axioms SortingAdversary.Optimal.Accounting.pool_entropy_le_root
#print axioms SortingAdversary.Optimal.GroupEntropy.conditional_entropy_le
#print axioms SortingAdversary.Optimal.GroupEntropy.selected_label_count_le
#print axioms SortingAdversary.Optimal.Endpoints.terminal_product_log_count
#print axioms SortingAdversary.Optimal.Parameters.logarithmicStage_tendsto
#print axioms SortingAdversary.Optimal.comparison_guarantee_of_vanishing_accounting

#audit_optimal_axioms
