import SortingAdversary.Optimal.LedgerController
import SortingAdversary.Optimal.ControllerRun

/-!
# The ledger of the actual complete active execution

The logger follows the concrete controller responses along the observed query
list. The actual machine run proves acceptance and all tree correspondences.
The promotion and degree budgets therefore count emitted controller actions
and the final actual tree, with no supplied accounting certificate.
-/

namespace SortingAdversary.Optimal.LedgerRun

open PoolTree.Tree PoolTreeAccounting TreeChronology LedgerTreeBridge LedgerStoredHistory
open LedgerStoredReplay LedgerController RecursiveController ControllerMachine ControllerRun

variable {n : ℕ}

def runLog {p : Parameters} (s : Active p n) : History n → IncidenceLedger.State n → Log n
  | [], ledger => ⟨ledger, []⟩
  | observation :: rest, ledger =>
      let first := responseLog s observation.query ledger
      let tail := runLog (respond s observation.query).next rest first.ledger
      ⟨tail.ledger, first.actions ++ tail.actions⟩

theorem runLog_calls {p : Parameters} (s : Active p n) (observations : History n)
    (ledger : IncidenceLedger.State n) :
    (runLog s observations ledger).ledger.calls.length = ledger.calls.length + observations.length := by
  induction observations generalizing s ledger with
  | nil => simp [runLog]
  | cons observation rest ih =>
    dsimp only [runLog]
    rw [ih]
    change (logFor (respond s observation.query).record ledger).ledger.calls.length + _ = _
    rw [logFor_calls_length]
    simp only [List.length_cons]
    omega

structure Outcome (threshold : ℕ) {p : Parameters} (s final : Active p n)
    (observations : History n) (ledger : IncidenceLedger.State n) : Prop where
  accepted : IncidenceLedger.run threshold ledger (runLog s observations ledger).actions =
    some (runLog s observations ledger).ledger
  represents : Represents (runLog s observations ledger).ledger final.tree.erase
  allocated : Allocated final.tree.erase final.counter
  recorded : Recorded (runLog s observations ledger).ledger.calls final.tree
  calls : (runLog s observations ledger).ledger.calls.length = ledger.calls.length + observations.length

theorem activeRun_spec (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    {s final : Active p n} {observations : History n} (run : ActiveRun p s observations final)
    (ledger : IncidenceLedger.State n) (halloc : Allocated s.tree.erase s.counter)
    (hrep : Represents ledger s.tree.erase) (hrecorded : Recorded ledger.calls s.tree) :
    Outcome threshold s final observations ledger := by
  induction run generalizing ledger with
  | nil s => exact ⟨rfl, hrep, halloc, hrecorded, by simp [runLog]⟩
  | cons s q tail ih =>
    have first := LedgerController.respond_spec threshold hthreshold s q ledger halloc hrep hrecorded
    have rest := ih (responseLog s q ledger).ledger first.allocated first.represents first.recorded
    refine ⟨?_, rest.represents, rest.allocated, rest.recorded, runLog_calls s _ ledger⟩
    change IncidenceLedger.run threshold ledger
      ((responseLog s q ledger).actions ++ (runLog (respond s q).next _ (responseLog s q ledger).ledger).actions) = _
    have hfirst : IncidenceLedger.run threshold ledger (responseLog s q ledger).actions =
        some (responseLog s q ledger).ledger := first.accepted
    rw [run_append, hfirst, Option.bind_some]
    exact rest.accepted

def initialLedger (N : ℕ) : IncidenceLedger.State (N + 2) :=
  IncidenceLedger.initial (initialFree (N + 2))

def initialLog (p : Parameters) (N : ℕ) (observations : History (N + 2)) : Log (N + 2) :=
  runLog (initialActive p N) observations (initialLedger N)

theorem initial_spec (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    Outcome p.repair.D (initialActive p N) final observations (initialLedger N) := by
  apply activeRun_spec p.repair.D le_rfl run
  · simpa only [initialActive, StoredTree.erase_initial] using TreeChronology.initial_allocated N
  · simpa only [initialActive, StoredTree.erase_initial, initialLedger] using initial_represents N
  · exact LedgerStoredHistory.initial_recorded N

theorem initial_valid (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    IncidenceLedger.Valid p.repair.D (initialLog p N observations).ledger :=
  IncidenceLedger.run_valid _ (IncidenceLedger.initial_valid _ _) (initial_spec p N run).accepted

theorem initial_complete (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    Complete (initialLog p N observations).ledger :=
  run_complete _ (IncidenceLedger.initial_valid _ _) (LedgerTreeBridge.initial_complete _)
    (initial_spec p N run).accepted

theorem actual_calls (p : Parameters) (N : ℕ) (observations : History (N + 2)) :
    (initialLog p N observations).ledger.calls.length = observations.length := by
  simpa only [initialLog, initialLedger, IncidenceLedger.initial, List.length_nil, zero_add] using
    runLog_calls (initialActive p N) observations (initialLedger N)

theorem actual_physical_count (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    ((initialLog p N observations).actions.map IncidenceLedger.Action.physicalCost).sum = observations.length := by
  have hc := IncidenceLedger.run_counts _ (IncidenceLedger.initial_valid _ _) (initial_spec p N run).accepted
  have he : (initialLog p N observations).ledger.calls.length =
      ((initialLog p N observations).actions.map IncidenceLedger.Action.physicalCost).sum := by
    simpa only [initialLog, initialLedger, IncidenceLedger.initial, List.length_nil, zero_add] using hc.1
  exact he.symm.trans (actual_calls p N observations)

theorem actual_promotions (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    (initialLog p N observations).ledger.moves.card = promotions final.tree.erase := by
  have hs := initial_spec p N run
  exact represented_moves_eq_promotions (initial_valid p N run) (initial_complete p N run)
    final.wellFormed hs.allocated hs.represents

theorem actual_promotion_count (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    ((initialLog p N observations).actions.map IncidenceLedger.Action.promotionCost).sum =
      promotions final.tree.erase := by
  have hs := initial_spec p N run
  exact actual_tree_promotion_count p.repair.D (initialFree (N + 2)) _ _ hs.accepted
    final.tree.erase final.wellFormed final.counter hs.allocated hs.represents

/-- Both budgets are derived from the emitted controller run. In particular,
`degreeMoves` is the exact set of actual degree-selected promotion events. -/
theorem actual_budgets (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)} (run : ActiveRun p (initialActive p N) observations final) :
    promotions final.tree.erase ≤ 2 * observations.length ∧
      p.repair.D * (IncidenceLedger.degreeMoves (initialLog p N observations).ledger).card ≤
        2 * observations.length := by
  have hb := IncidenceLedger.accepted_run_budgets p.repair.D (initialFree (N + 2))
    (initialLog p N observations).actions (initialLog p N observations).ledger (initial_spec p N run).accepted
  simpa only [actual_promotions p N run, actual_calls] using hb

end SortingAdversary.Optimal.LedgerRun
