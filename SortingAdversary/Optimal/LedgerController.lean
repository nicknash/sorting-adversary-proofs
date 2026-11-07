import SortingAdversary.Optimal.LedgerRouter
import SortingAdversary.Optimal.ControllerMachine

/-!
# Every concrete controller response advances the accepted ledger

Known physical comparisons append an empty incidence row. Unknown comparisons
append their actual stopping row and replay exactly the emitted repairs.
Materialization is extensionally the same stored tree, so the representation,
source history, and fresh-identity allocator are preserved by every response.
-/

namespace SortingAdversary.Optimal.LedgerController

open TreeChronology LedgerTreeBridge LedgerTreeTransitions LedgerStoredHistory
open LedgerStoredReplay LedgerQuery LedgerRouter RecursiveController ControllerMachine

variable {n : ℕ}

def logFor {p : Parameters} (record : Option (RepairRecord p n))
    (ledger : IncidenceLedger.State n) : Log n :=
  match record with
  | none => ⟨physicalLedger ledger none, [.physical none]⟩
  | some r => recordLog r ledger

def responseLog {p : Parameters} (s : Active p n) (q : Query n)
    (ledger : IncidenceLedger.State n) : Log n := logFor (respond s q).record ledger

theorem logFor_calls_length {p : Parameters} (record : Option (RepairRecord p n))
    (ledger : IncidenceLedger.State n) :
    (logFor record ledger).ledger.calls.length = ledger.calls.length + 1 := by
  cases record with
  | none => simp [logFor, physicalLedger]
  | some record => exact recordLog_calls_length record ledger

structure Outcome (threshold : ℕ) {p : Parameters} {s : Active p n} {q : Query n}
    (response : Response s q) (ledger : IncidenceLedger.State n) : Prop where
  accepted : IncidenceLedger.run threshold ledger (logFor response.record ledger).actions =
    some (logFor response.record ledger).ledger
  represents : Represents (logFor response.record ledger).ledger response.next.tree.erase
  allocated : Allocated response.next.tree.erase response.next.counter
  recorded : Recorded (logFor response.record ledger).ledger.calls response.next.tree
  calls : (logFor response.record ledger).ledger.calls.length = ledger.calls.length + 1
  charge : match response.record with
    | none => response.charge = 1
    | some r => response.charge = (1 / (1 / 2 - p.error)) * r.replay.charge
  origin : ∀ r, response.record = some r → Origin r ledger

theorem respond_spec (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    (s : Active p n) (q : Query n) (ledger : IncidenceLedger.State n)
    (halloc : Allocated s.tree.erase s.counter) (hrep : Represents ledger s.tree.erase)
    (hrecorded : Recorded ledger.calls s.tree) : Outcome threshold (respond s q) ledger := by
  have hc := logFor_calls_length (respond s q).record ledger
  have hknown : IncidenceLedger.run threshold ledger [.physical none] =
      some (physicalLedger ledger none) := by
    rw [IncidenceLedger.run, step_physicalLedger threshold ledger none trivial, Option.bind_some]
    rfl
  have hknownrep := physicalLedger_represents ledger s.tree.erase none hrep
  have hknownrecorded := hrecorded.append [none]
  by_cases hl : s.tree.pool.system.edge q.left q.right = true
  · erw [respond, dif_pos hl]
    exact ⟨hknown, hknownrep, halloc, hknownrecorded, by simp [logFor, physicalLedger], rfl, by intros r h; contradiction⟩
  · by_cases hg : s.tree.pool.system.edge q.right q.left = true
    · erw [respond, dif_neg hl, dif_pos hg]
      exact ⟨hknown, hknownrep, halloc, hknownrecorded, by simp [logFor, physicalLedger], rfl, by intros r h; contradiction⟩
    · let result := answerUnknown p s.tree s.wellFormed s.coherent s.normal q.left q.right
        (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
        hl hg s.counter
      have hs := answerUnknown_spec threshold .top p hthreshold s.tree s.wellFormed s.coherent s.normal
        q.left q.right (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
        hl hg s.counter ledger halloc hrep hrecorded
      erw [respond, dif_neg hl, dif_neg hg]
      refine ⟨hs.accepted, ?_, ?_, ?_, recordLog_calls_length result.payload ledger, hs.charge, ?_⟩
      · change Represents (recordLog result.payload ledger).ledger result.next.materialize.erase
        rw [ControllerMachine.materialize_eq]
        exact hs.represents
      · change Allocated result.next.materialize.erase result.counter
        rw [ControllerMachine.materialize_eq]
        exact hs.allocated
      · change Recorded (recordLog result.payload ledger).ledger.calls result.next.materialize
        rw [ControllerMachine.materialize_eq]
        exact hs.recorded
      · intro r hr
        have he : result.payload = r := Option.some.inj hr
        subst r
        exact hs.origin

end SortingAdversary.Optimal.LedgerController
