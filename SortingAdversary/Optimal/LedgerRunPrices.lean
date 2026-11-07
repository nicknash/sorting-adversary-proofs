import SortingAdversary.Optimal.LedgerControllerPrices

/-!
# Exact signed accounting over the actual complete active run

Every physical response contributes its real primitive repair receipts. The
birthday credits telescope to the final factorial potential and the signed
receipt bounds telescope to the actual counting-potential drop.
-/

namespace SortingAdversary.Optimal.LedgerRunPrices

open PoolTree.Tree PoolTreeAccounting TreeChronology LedgerTreeBridge LedgerStoredHistory
open LedgerController LedgerRun LedgerBirthCredits LedgerReplayPrices LedgerControllerPrices
open RecursiveController ControllerMachine ControllerRun

variable {n : ℕ}

def runReceipts {p : Parameters} (s : Active p n) : History n → List (Receipt n)
  | [] => []
  | observation :: rest => responseReceipts s observation.query ++
      runReceipts (respond s observation.query).next rest

theorem activeRun_credit (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    {s final : Active p n} {observations : History n} (run : ActiveRun p s observations final)
    (ledger : IncidenceLedger.State n) (halloc : Allocated s.tree.erase s.counter)
    (hrep : Represents ledger s.tree.erase) (hrecorded : Recorded ledger.calls s.tree) :
    factorialCredit (runLog s observations ledger).ledger = factorialCredit ledger +
      ((runReceipts s observations).map Receipt.credit).sum := by
  induction run generalizing ledger with
  | nil => simp [runLog, runReceipts]
  | cons s q tail ih =>
    have hs := LedgerController.respond_spec threshold hthreshold s q ledger halloc hrep hrecorded
    have hh := response_credit threshold hthreshold s q ledger halloc hrep hrecorded
    have ht := ih (responseLog s q ledger).ledger hs.allocated hs.represents hs.recorded
    dsimp only [runLog, runReceipts]
    rw [List.map_append, List.sum_append, ht, hh]
    ring

theorem activeRun_signed (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    {s final : Active p n} {observations : History n} (run : ActiveRun p s observations final)
    (ledger : IncidenceLedger.State n) (halloc : Allocated s.tree.erase s.counter)
    (hrep : Represents ledger s.tree.erase) (hrecorded : Recorded ledger.calls s.tree) :
    Real.log (s.tree.erase.count : ℝ) - Real.log (final.tree.erase.count : ℝ) ≤
      (observations.length : ℝ) * physicalPrice p + ((runReceipts s observations).map Receipt.debit).sum -
        (factorialCredit (runLog s observations ledger).ledger - factorialCredit ledger) := by
  induction run generalizing ledger with
  | nil => simp [runLog, runReceipts]
  | cons s q tail ih =>
    have hs := LedgerController.respond_spec threshold hthreshold s q ledger halloc hrep hrecorded
    have hh := response_signed threshold hthreshold s q ledger halloc hrep hrecorded
    have ht := ih (responseLog s q ledger).ledger hs.allocated hs.represents hs.recorded
    dsimp only [runLog, runReceipts]
    simp only [List.map_append, List.sum_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem initial_credit (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    factorialCredit (initialLog p N observations).ledger = factorialCredit (initialLedger N) +
      ((runReceipts (initialActive p N) observations).map Receipt.credit).sum := by
  apply activeRun_credit p.repair.D le_rfl run
  · simpa only [initialActive, StoredTree.erase_initial] using TreeChronology.initial_allocated N
  · simpa only [initialActive, StoredTree.erase_initial, initialLedger] using initial_represents N
  · exact LedgerStoredHistory.initial_recorded N

theorem initial_signed (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    Real.log ((initialActive p N).tree.erase.count : ℝ) - Real.log (final.tree.erase.count : ℝ) ≤
      (observations.length : ℝ) * physicalPrice p +
        ((runReceipts (initialActive p N) observations).map Receipt.debit).sum -
        (factorialCredit (initialLog p N observations).ledger - factorialCredit (initialLedger N)) := by
  apply activeRun_signed p.repair.D le_rfl run
  · simpa only [initialActive, StoredTree.erase_initial] using TreeChronology.initial_allocated N
  · simpa only [initialActive, StoredTree.erase_initial, initialLedger] using initial_represents N
  · exact LedgerStoredHistory.initial_recorded N

end SortingAdversary.Optimal.LedgerRunPrices
