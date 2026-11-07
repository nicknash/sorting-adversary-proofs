import SortingAdversary.Optimal.ControllerLedgerAlignment
import SortingAdversary.Optimal.RepairEventCounts
import SortingAdversary.Optimal.ReservationEntropyRun

/-!
# Actual expensive counts and their incidence/entropy budgets

The summary classifications are the same labels replayed by the accepted
ledger. The path and scale totals are the counts of the actual chronological
reservation lists. This identifies every population in the final expensive
budget with the concrete controller execution.
-/

namespace SortingAdversary.Optimal.ControllerEventCounts

open WidthRepair PoolTree.Tree PoolTreeAccounting LedgerTreeTransitions LedgerStoredReplay
open LedgerReplayLabels LedgerStructuralReplay LedgerQuery LedgerController LedgerRun
open RecursiveController ControllerMachine ControllerRun ControllerPricing RepairPricing RepairEventCounts
open ReservationController ReservationFinalGroups ReservationEntropyRun

variable {n : ℕ}

def kindCost (kind : IncidenceLedger.Kind) : IncidenceLedger.Action n → ℕ
  | .promote _ actual => if actual = kind then 1 else 0
  | _ => 0

def runKind {p : Parameters} (s : Active p n) (history : History n) (kind : IncidenceLedger.Kind) : ℕ :=
  ((runRecords s history).map (fun record =>
    kindCount record.result.trace (structuralLabels record.result.events) kind)).sum

theorem replay_kinds (identity : ℕ) {s t : WidthRepair.State n} (trace : Trace s t)
    (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ledger : IncidenceLedger.State n) (kind : IncidenceLedger.Kind) :
    ((replayLedger identity trace labels children hw ho counter ledger).actions.map (kindCost kind)).sum =
      kindCount trace labels kind := by
  induction trace generalizing children counter ledger with
  | nil => rfl
  | cons head tail ih =>
    dsimp only [replayLedger]
    rw [List.map_append, List.sum_append, ih]
    cases head <;> simp [stepActions, promotionActions, kindCost, kindCount, stepKindCount]

theorem record_kinds {p : Parameters} (record : RepairRecord p n) (ledger : IncidenceLedger.State n)
    (kind : IncidenceLedger.Kind) :
    ((recordLog record ledger).actions.map (kindCost kind)).sum =
      kindCount record.result.trace (structuralLabels record.result.events) kind := by
  change ((.physical (physicalRow record) :: _).map (kindCost kind)).sum = _
  simp only [List.map_cons, List.sum_cons, kindCost, zero_add]
  exact replay_kinds record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter _ kind

theorem run_kinds {p : Parameters} (s : Active p n) (history : History n)
    (ledger : IncidenceLedger.State n) (kind : IncidenceLedger.Kind) :
    ((runLog s history ledger).actions.map (kindCost kind)).sum = runKind s history kind := by
  induction history generalizing s ledger with
  | nil => rfl
  | cons observed rest ih =>
    simp only [runLog, List.map_append, List.sum_append, ih, runKind, runRecords]
    cases hr : (respond s observed.query).record with
    | none => simp [responseLog, hr, logFor, kindCost]
    | some record => simp only [responseLog, hr, logFor, Option.toList_some, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, record_kinds]

theorem degreeCost_eq (action : IncidenceLedger.Action n) :
    kindCost .degree action = action.degreeCost := by
  cases action with
  | admit => rfl
  | physical => rfl
  | promote location kind => cases kind <;> rfl

theorem promotionCost_eq (action : IncidenceLedger.Action n) :
    action.promotionCost = kindCost .cheap action + kindCost .degree action +
      kindCost .path action + kindCost .scale action := by
  cases action with
  | admit => rfl
  | physical => rfl
  | promote location kind => cases kind <;> rfl

theorem run_cheap_eq {p : Parameters} (s : Active p n) (history : History n) :
    runCheap s history = runKind s history .cheap := by
  unfold runCheap runKind
  congr 1
  exact List.map_congr_left (fun record _ => (structural_recorded p.repair record.result.events).cheap)

theorem run_hubs_eq {p : Parameters} (s : Active p n) (history : History n) :
    (runHubs s history).length = runKind s history .degree + runKind s history .path +
      runKind s history .scale := by
  simp only [runHubs, List.length_flatMap, recordHubs, List.length_map]
  have he : ((runRecords s history).map (fun r => (recordSummary r).hubs.length)).sum =
      ((runRecords s history).map (fun r =>
        kindCount r.result.trace (structuralLabels r.result.events) .degree +
        kindCount r.result.trace (structuralLabels r.result.events) .path +
        kindCount r.result.trace (structuralLabels r.result.events) .scale)).sum := by
    congr 1
    exact List.map_congr_left (fun record _ => (structural_recorded p.repair record.result.events).hubs)
  rw [he, List.sum_map_add, List.sum_map_add]
  rfl

theorem run_scale_eq {p : Parameters} (s : Active p n) (history : History n) :
    runScale s history = runKind s history .scale := by
  simp only [runScale, runHubs, List.filter_flatMap, List.length_flatMap, recordHubs,
    List.filter_map, List.length_map]
  change ((runRecords s history).map (fun r => scaleCount (recordSummary r).hubs)).sum = _
  unfold runKind
  congr 1
  exact List.map_congr_left (fun record _ => (structural_recorded p.repair record.result.events).scale)

theorem historyPaths_records {p : Parameters} (s : Active p n) (history : History n) :
    historyPaths s history = (runRecords s history).flatMap recordPaths := by
  induction history generalizing s with
  | nil => rfl
  | cons observed rest ih =>
    simp only [historyPaths, runRecords, List.flatMap_append, ih]
    cases hr : (respond s observed.query).record <;> simp [responsePaths, hr]

theorem historyScales_records {p : Parameters} (s : Active p n) (history : History n) :
    historyScales s history = (runRecords s history).flatMap recordScales := by
  induction history generalizing s with
  | nil => rfl
  | cons observed rest ih =>
    simp only [historyScales, runRecords, List.flatMap_append, ih]
    cases hr : (respond s observed.query).record <;> simp [responseScales, hr]

theorem run_path_le {p : Parameters} (s : Active p n) (history : History n) :
    runKind s history .path ≤ p.repair.H * (historyPaths s history).length := by
  rw [historyPaths_records, List.length_flatMap, ← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro record _
  simpa only [recordPaths, ReservationMachine.pathGroups, ReservationStoredReplay.locations,
    List.length_map] using structural_path_count record.result.events

theorem run_scale_groups {p : Parameters} (s : Active p n) (history : History n) :
    runKind s history .scale = p.repair.scale.J * (historyScales s history).length := by
  rw [historyScales_records, List.length_flatMap, ← List.sum_map_mul_left]
  unfold runKind
  congr 1
  apply List.map_congr_left
  intro record _
  simpa only [recordScales, ReservationMachine.scaleGroups, ReservationStoredReplay.locations,
    List.length_map] using structural_scale_count record.result.events

theorem actual_degree_count (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    runKind (initialActive p N) observations .degree =
      (IncidenceLedger.degreeMoves (initialLog p N observations).ledger).card := by
  have hc := IncidenceLedger.run_counts _ (IncidenceLedger.initial_valid _ _) (initial_spec p N history).accepted
  have he : (IncidenceLedger.degreeMoves (initialLog p N observations).ledger).card =
      ((initialLog p N observations).actions.map IncidenceLedger.Action.degreeCost).sum := by
    simpa only [initialLog, initialLedger, IncidenceLedger.initial, IncidenceLedger.degreeMoves,
      Finset.filter_empty, Finset.card_empty, zero_add] using hc.2.2
  rw [he, ← run_kinds (initialActive p N) observations (initialLedger N) .degree]
  have hf : kindCost .degree = (IncidenceLedger.Action.degreeCost : IncidenceLedger.Action (N + 2) → ℕ) :=
    funext degreeCost_eq
  rw [hf]
  rfl

theorem actual_cheap_add_hubs (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    runCheap (initialActive p N) observations + (runHubs (initialActive p N) observations).length =
      promotions final.tree.erase := by
  rw [← actual_promotion_count p N history, run_cheap_eq, run_hubs_eq]
  have hf : (IncidenceLedger.Action.promotionCost : IncidenceLedger.Action (N + 2) → ℕ) =
      fun a => kindCost .cheap a + kindCost .degree a + kindCost .path a + kindCost .scale a :=
    funext promotionCost_eq
  rw [hf]
  simp only [List.sum_map_add]
  change _ = (((runLog (initialActive p N) observations (initialLedger N)).actions.map (kindCost .cheap)).sum +
    ((runLog (initialActive p N) observations (initialLedger N)).actions.map (kindCost .degree)).sum +
    ((runLog (initialActive p N) observations (initialLedger N)).actions.map (kindCost .path)).sum +
    ((runLog (initialActive p N) observations (initialLedger N)).actions.map (kindCost .scale)).sum)
  rw [run_kinds, run_kinds, run_kinds, run_kinds]
  omega

theorem actual_hub_budget (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    ((runHubs (initialActive p N) observations).length : ℝ) ≤
      2 * observations.length / p.repair.D +
        (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) / Real.log (p.repair.H : ℝ) +
        (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
          Real.log ((p.repair.scale.J : ℝ) / 2) := by
  have hdeg := IncidenceLedger.degree_moves_le (LedgerRun.initial_valid p N history) p.repair.degree_pos
  rw [actual_calls] at hdeg
  have hp := actual_path_labels_le p N history
  have hs := actual_scale_labels_le p N history (by have h := p.repair.scale.group; omega)
  have hpath : (runKind (initialActive p N) observations .path : ℝ) ≤
      p.repair.H * (historyPaths (initialActive p N) observations).length := by
    exact_mod_cast run_path_le (initialActive p N) observations
  rw [run_hubs_eq, Nat.cast_add, Nat.cast_add, actual_degree_count p N history,
    run_scale_groups, Nat.cast_mul]
  nlinarith

theorem actual_scale_budget (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    (runScale (initialActive p N) observations : ℝ) ≤
      (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
        Real.log ((p.repair.scale.J : ℝ) / 2) := by
  rw [run_scale_eq, run_scale_groups, Nat.cast_mul]
  simpa only [mul_comm] using actual_scale_labels_le p N history
    (by have h := p.repair.scale.group; omega)

theorem actual_cheap_hubs_le_twice_calls (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    runCheap (initialActive p N) observations + (runHubs (initialActive p N) observations).length ≤
      2 * observations.length := by
  rw [actual_cheap_add_hubs p N history]
  exact (actual_budgets p N history).1

end SortingAdversary.Optimal.ControllerEventCounts
