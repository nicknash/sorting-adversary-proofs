import SortingAdversary.Optimal.RepairSignedPrice
import SortingAdversary.Optimal.RepairCuts
import SortingAdversary.Optimal.RepairEvolution
import SortingAdversary.Optimal.ControllerEvolution

/-!
# Actual chronological repair and hub histories

The history below is extracted by re-running the deterministic response on
each recorded query. Its certificates show that every emitted hub belongs to
a real final node with the same immutable identity and physical destination.
-/

namespace SortingAdversary.Optimal.ControllerPricing

open scoped BigOperators
open WidthRepair RecursiveController ControllerMachine ControllerRun StoredEvolution
open RepairPricing

variable {n : ℕ} {p : Parameters}

def recordSummary (record : RepairRecord p n) :=
  Summary.fromEvents p.repair record.result.events

def runRecords (s : Active p n) : History n → List (RepairRecord p n)
  | [] => []
  | observation :: tail =>
    (respond s observation.query).record.toList ++
      runRecords (respond s observation.query).next tail

def recordHubs (record : RepairRecord p n) : List (ℕ × HubEvent n) :=
  (recordSummary record).hubs.map (fun event => (record.identity, event))

def runHubs (s : Active p n) (history : History n) : List (ℕ × HubEvent n) :=
  (runRecords s history).flatMap recordHubs

def runCheap (s : Active p n) (history : History n) : ℕ :=
  ((runRecords s history).map (fun record => (recordSummary record).cheap)).sum

def runCuts (s : Active p n) (history : History n) : ℕ :=
  ((runRecords s history).map (fun record => (recordSummary record).cuts)).sum

def runScale (s : Active p n) (history : History n) : ℕ :=
  ((runHubs s history).filter (fun tagged => tagged.2.scale)).length

noncomputable def runDebit (s : Active p n) (history : History n) : ℝ :=
  ((runRecords s history).map (fun record => logCharge record.result.trace)).sum

theorem runRecords_length (s : Active p n) (history : History n) :
    (runRecords s history).length ≤ history.length := by
  induction history generalizing s with
  | nil => simp [runRecords]
  | cons observation tail ih =>
    have h := ih (respond s observation.query).next
    cases hr : (respond s observation.query).record <;> simp [runRecords, hr] <;> omega

/-- A repair record's final state evolves at its real stored node through all
later physical queries in the actual run. -/
theorem runRecords_final {s final : Active p n} {history : History n}
    (run : ActiveRun p s history final) (record : RepairRecord p n)
    (member : record ∈ runRecords s history) :
    ∃ state, NodeAt final.tree record.identity state ∧
      LocalEvolution record.result.final state := by
  induction run with
  | nil => simp [runRecords] at member
  | cons current query tail ih =>
    change record ∈ (respond current query).record.toList ++ _ at member
    rcases List.mem_append.mp member with head | rest
    · have hr : (respond current query).record = some record := by
        simpa using head
      exact ControllerEvolution.activeRun_evolves tail _ _
        (ControllerEvolution.respond_site current query record hr).2
    · exact ih rest

theorem runHubs_fit {s final : Active p n} {history : History n}
    (run : ActiveRun p s history final) (tagged : ℕ × HubEvent n)
    (member : tagged ∈ runHubs s history) :
    ∃ state, NodeAt final.tree tagged.1 state ∧ tagged.2.Fits state := by
  obtain ⟨record, hr, he⟩ := List.mem_flatMap.mp member
  change tagged ∈ (recordSummary record).hubs.map (fun event => (record.identity, event)) at he
  obtain ⟨event, hm, rfl⟩ := List.mem_map.mp he
  obtain ⟨state, occurs, evolution⟩ := runRecords_final run record hr
  exact ⟨state, occurs, ((recordSummary record).fits event hm).evolution evolution⟩

theorem runRecords_cut_budget (record : RepairRecord p n) :
    (recordSummary record).cuts +
      (SparseRepairGraph.rawRows record.result.final.rows.active).card ≤
      (SparseRepairGraph.rawRows
        (compared record.before record.first record.second record.first_member
          record.second_member record.distinct record.updated).rows.active).card :=
  Summary.fromEvents_cut_budget p.repair record.result.events

end SortingAdversary.Optimal.ControllerPricing
