import SortingAdversary.Optimal.LedgerPromotionTrace
import SortingAdversary.Optimal.TreeFactorialCredit
import SortingAdversary.Optimal.ControllerPricing
import SortingAdversary.Optimal.RepairHubPins

/-!
# One actual history for the incidence, receipt, and hub accounts

The controller's emitted repair records, primitive pin list, accepted ledger
promotions, and signed receipts are identified here. In particular, expensive
hub locations form a sublist of the unique actual promotion-location list,
and receipt debits are exactly the actual parent repair log charges.
-/

namespace SortingAdversary.Optimal.ControllerLedgerAlignment

open WidthRepair PoolTree.Tree PoolTreeTraversal LedgerTreeTransitions LedgerStoredReplay
open LedgerReplayLabels LedgerStructuralReplay LedgerQuery LedgerController LedgerRun
open LedgerReplayPrices LedgerControllerPrices LedgerRunPrices LedgerPromotionTrace
open RecursiveController ControllerMachine ControllerRun ControllerPricing RepairPricing RepairHubPins
open TreeFactorialCredit

variable {n : ℕ}

theorem replay_promotions (identity : ℕ) {s t : WidthRepair.State n} (trace : Trace s t)
    (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ledger : IncidenceLedger.State n) :
    promotionLocations (replayLedger identity trace labels children hw ho counter ledger).actions =
      (pinVertices trace).map (fun v => (identity, v)) := by
  induction trace generalizing children counter ledger with
  | nil => rfl
  | cons head tail ih =>
    dsimp only [replayLedger]
    rw [promotionLocations_append, ih]
    cases head <;> simp only [stepActions, promotionActions, promotionLocations, List.filterMap_cons,
      List.filterMap_nil, promotedLocation, pinVertices, stepPins, List.map_append,
      List.map_cons, List.map_nil, List.nil_append, List.singleton_append]

theorem record_promotions {p : Parameters} (record : RepairRecord p n) (ledger : IncidenceLedger.State n) :
    promotionLocations (recordLog record ledger).actions =
      (pinVertices record.result.trace).map (fun v => (record.identity, v)) := by
  change promotionLocations (.physical (physicalRow record) :: _) = _
  simp only [promotionLocations, List.filterMap_cons, promotedLocation]
  exact replay_promotions record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter _

theorem run_promotions {p : Parameters} (s : Active p n) (history : History n)
    (ledger : IncidenceLedger.State n) :
    promotionLocations (runLog s history ledger).actions =
      (runRecords s history).flatMap (fun record =>
        (pinVertices record.result.trace).map (fun v => (record.identity, v))) := by
  induction history generalizing s ledger with
  | nil => rfl
  | cons observed rest ih =>
    simp only [runLog, promotionLocations_append, runRecords, List.flatMap_append, ih]
    cases hr : (respond s observed.query).record with
    | none => simp [responseLog, hr, logFor, promotionLocations, promotedLocation]
    | some record => simp only [responseLog, hr, logFor, Option.toList_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, record_promotions]

theorem record_hubs_sublist {p : Parameters} (record : RepairRecord p n) :
    ((recordHubs record).map (fun tagged => (tagged.1, tagged.2.vertex))).Sublist
      ((pinVertices record.result.trace).map (fun v => (record.identity, v))) := by
  have h := (fromEvents_hubs_sublist p.repair record.result.events).map (fun v => (record.identity, v))
  simpa only [recordHubs, recordSummary, List.map_map, Function.comp_def] using h

theorem run_hubs_sublist {p : Parameters} (s : Active p n) (history : History n)
    (ledger : IncidenceLedger.State n) :
    ((runHubs s history).map (fun tagged => (tagged.1, tagged.2.vertex))).Sublist
      (promotionLocations (runLog s history ledger).actions) := by
  rw [run_promotions]
  simp only [runHubs, List.map_flatMap]
  induction runRecords s history with
  | nil => exact List.Sublist.refl _
  | cons record rest ih => exact (record_hubs_sublist record).append ih

/-- Every expensive hub in the actual complete run has a distinct physical
`(node identity, label)` location. -/
theorem actual_hub_locations_nodup (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    ((runHubs (initialActive p N) observations).map (fun tagged => (tagged.1, tagged.2.vertex))).Nodup :=
  (actual_promotion_locations_nodup p N history).sublist
    (run_hubs_sublist (initialActive p N) observations (initialLedger N))

theorem replay_debits (identity : ℕ) {s t : WidthRepair.State n} (trace : Trace s t)
    (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    ((replayReceipts identity trace labels children hw ho counter).map Receipt.debit).sum =
      logCharge trace := by
  induction trace generalizing children counter with
  | nil => simp [replayReceipts, logCharge, Trace.charge]
  | cons head tail ih =>
    dsimp only [replayReceipts]
    rw [List.map_cons, List.sum_cons, ih]
    change Real.log ((stepReceipt identity head labels.1 children counter).charge : ℝ) +
      Real.log (tail.charge : ℝ) = Real.log ((head.charge * tail.charge : ℚ) : ℝ)
    have hh : (0 : ℝ) < head.charge := by exact_mod_cast head.charge_pos
    have ht : (0 : ℝ) < tail.charge := by exact_mod_cast trace_charge_pos tail
    rw [stepReceipt_charge, Rat.cast_mul, Real.log_mul hh.ne' ht.ne']

theorem record_debits {p : Parameters} (record : RepairRecord p n) :
    ((recordReceipts record).map Receipt.debit).sum = logCharge record.result.trace :=
  replay_debits record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter

theorem runReceipts_flatMap {p : Parameters} (s : Active p n) (history : History n) :
    runReceipts s history = (runRecords s history).flatMap recordReceipts := by
  induction history generalizing s with
  | nil => rfl
  | cons observed rest ih =>
    simp only [runReceipts, runRecords, List.flatMap_append, ih]
    cases hr : (respond s observed.query).record <;> simp [responseReceipts, hr]

theorem run_debits {p : Parameters} (s : Active p n) (history : History n) :
    ((runReceipts s history).map Receipt.debit).sum = runDebit s history := by
  rw [runReceipts_flatMap, sum_map_flatMap]
  unfold runDebit
  congr 1
  exact List.map_congr_left (fun record _ => record_debits record)

/-- The complete actual finite execution satisfies the signed accounting
inequality in the same variables used by its expensive-hub history. -/
theorem actual_signed (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun p (initialActive p N) observations final) :
    ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) - Real.log (final.tree.erase.count : ℝ) ≤
      (observations.length : ℝ) * physicalPrice p + runDebit (initialActive p N) observations -
        nonrootFactorial final.tree.erase := by
  have h := LedgerRunPrices.initial_signed p N history
  rw [run_debits, actual_factorial_difference p N history] at h
  simpa only [initialActive, StoredTree.erase_initial, PoolTree.Tree.initial_count,
    Nat.cast_pow, Real.log_pow] using h

end SortingAdversary.Optimal.ControllerLedgerAlignment
