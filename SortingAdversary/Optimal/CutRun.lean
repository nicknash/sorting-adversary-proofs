import SortingAdversary.Optimal.CutAccounting
import SortingAdversary.Optimal.ControllerPricing

/-!
# Actual whole-run cut count

The cuts in the common chronological repair history are bounded by the
physical comparisons in that same controller execution. The proof telescopes
the actual active-row potential, starting from the empty root source graph.
-/

namespace SortingAdversary.Optimal.CutAccounting

open RecursiveController ControllerMachine ControllerRun ControllerPricing StoredRowPotential

variable {n : ℕ}

theorem runCuts_cons {p : Parameters} (s : Active p n) (observation : Observation n)
    (rest : History n) :
    runCuts s (observation :: rest) = optionCuts (respond s observation.query).record +
      runCuts (respond s observation.query).next rest := by
  simp only [runCuts, runRecords, List.map_append, List.sum_append]
  cases h : (respond s observation.query).record <;>
    simp only [Option.toList_none, Option.toList_some, List.map_nil, List.map_cons,
      List.sum_nil, List.sum_cons, Nat.add_zero, optionCuts, recordCuts, recordSummary]

theorem activeRun_cut_budget {p : Parameters} {s final : Active p n} {observations : History n}
    (run : ActiveRun p s observations final) :
    runCuts s observations + rows final.tree ≤ rows s.tree + observations.length := by
  induction run with
  | nil s => simp [runCuts, runRecords]
  | cons s q tail ih =>
    rw [runCuts_cons, List.length_cons]
    dsimp only
    have h := respond_budget s q
    omega

/-- No accepted-history or aggregate cut premise: this counts the actual
repair records emitted by the initial concrete active execution. -/
theorem initial_cuts_le (p : Parameters) (N : ℕ) {final : Active p (N + 2)}
    {observations : History (N + 2)}
    (run : ActiveRun p (initialActive p N) observations final) :
    runCuts (initialActive p N) observations ≤ observations.length := by
  have h := activeRun_cut_budget run
  change runCuts (initialActive p N) observations + rows final.tree ≤
    rows (StoredTree.initial N) + observations.length at h
  rw [rows_initial, Nat.zero_add] at h
  omega

end SortingAdversary.Optimal.CutAccounting
