import SortingAdversary.Optimal.ReservationMachine
import SortingAdversary.Optimal.LedgerController

/-!
# Reservation execution for the actual routed controller response

The stopping-site origin is recovered by the concrete router. A physical
comparison changes the call history but leaves both reservation free sets
unchanged; the exact subsequent repair supplies the two event streams.
-/

namespace SortingAdversary.Optimal.ReservationController

open WidthRepair LedgerStoredReplay LedgerStructuralReplay ReservationStoredReplay
open ReservationMachine LedgerTreeBridge LedgerTreeTransitions LedgerStoredHistory TreeChronology
open RecursiveController ControllerMachine LedgerQuery

variable {n : ℕ}

def recordStreams {p : Parameters} (record : RepairRecord p n) : Streams n :=
  normalizerStreams record.identity record.result record.children
    record.wellFormed record.coherent record.counter

def recordPaths {p : Parameters} (record : RepairRecord p n) :
    List (Finset (IncidenceLedger.Location n)) := pathGroups record.identity record.result

def recordScales {p : Parameters} (record : RepairRecord p n) :
    List (Finset (IncidenceLedger.Location n)) := scaleGroups record.identity record.result

theorem record_accepted (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    (record : RepairRecord p n) (ledger : IncidenceLedger.State n) (origin : Origin record ledger)
    (books : Books n) (hbooks : Invariant p.repair.H p.repair.scale.J books ledger) :
    ∃ after : Books n, ReservationMachine.run books (recordStreams record) = some after ∧
      Invariant p.repair.H p.repair.scale.J after (recordLog record ledger).ledger ∧
      after.path.groups = (recordPaths record).reverse ++ books.path.groups ∧
      after.scale.groups = (recordScales record).reverse ++ books.scale.groups := by
  obtain ⟨ctx, ha, hrep, hrecorded⟩ := origin
  let after := compared record.before record.first record.second record.first_member record.second_member
    record.distinct record.updated
  let called := physicalLedger ledger (physicalRow record)
  have ha' : Allocated (ctx.plug (StoredRepair.node record.identity after record.children).erase)
      record.counter := by
    rw [StoredRepair.erase_node]
    apply allocated_poolUpdate ctx record.identity record.before.pool after.pool _ record.counter
    simpa only [StoredRepair.erase_node] using ha
  have hrep' : Represents called (ctx.plug (StoredRepair.node record.identity after record.children).erase) := by
    rw [StoredRepair.erase_node]
    apply represents_poolUpdate called ctx record.identity record.before.pool after.pool _ rfl rfl
    simpa only [StoredRepair.erase_node] using physicalLedger_represents ledger _ (physicalRow record) hrep
  have hrecorded' : Recorded called.calls (StoredRepair.node record.identity after record.children) :=
    hrecorded.stopNode record.first record.second record.first_member record.second_member
      record.distinct record.updated
  have hb : Invariant p.repair.H p.repair.scale.J books called :=
    ⟨hbooks.pathValid, hbooks.scaleValid,
      ⟨hbooks.pathSync.entered, hbooks.pathSync.free⟩,
      ⟨hbooks.scaleSync.entered, hbooks.scaleSync.free⟩,
      hbooks.pathDone, hbooks.scaleDone, hbooks.pathSize, hbooks.scaleSize⟩
  exact normalizer_accepted threshold ctx record.identity hthreshold record.result record.children
    record.wellFormed record.coherent record.counter ha' called hrep' hrecorded' books hb

def responseStreams {p : Parameters} (s : Active p n) (q : Query n) : Streams n :=
  match (respond s q).record with
  | none => ⟨[], []⟩
  | some record => recordStreams record

def responsePaths {p : Parameters} (s : Active p n) (q : Query n) :
    List (Finset (IncidenceLedger.Location n)) :=
  match (respond s q).record with
  | none => []
  | some record => recordPaths record

def responseScales {p : Parameters} (s : Active p n) (q : Query n) :
    List (Finset (IncidenceLedger.Location n)) :=
  match (respond s q).record with
  | none => []
  | some record => recordScales record

/-- The actual controller response supplies its own stopping-site origin.
The caller supplies only the previously established runtime invariants. -/
theorem response_accepted (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    (s : Active p n) (q : Query n) (ledger : IncidenceLedger.State n)
    (halloc : Allocated s.tree.erase s.counter) (hrep : Represents ledger s.tree.erase)
    (hrecorded : Recorded ledger.calls s.tree)
    (books : Books n) (hbooks : Invariant p.repair.H p.repair.scale.J books ledger) :
    ∃ after : Books n, ReservationMachine.run books (responseStreams s q) = some after ∧
      Invariant p.repair.H p.repair.scale.J after (LedgerController.responseLog s q ledger).ledger ∧
      after.path.groups = (responsePaths s q).reverse ++ books.path.groups ∧
      after.scale.groups = (responseScales s q).reverse ++ books.scale.groups := by
  have hs := LedgerController.respond_spec threshold hthreshold s q ledger halloc hrep hrecorded
  cases hr : (respond s q).record with
  | none =>
    refine ⟨books, ?_, ?_, ?_, ?_⟩
    · simp only [responseStreams, hr]
      rfl
    · refine ⟨hbooks.pathValid, hbooks.scaleValid, ?_, ?_, hbooks.pathDone, hbooks.scaleDone,
        hbooks.pathSize, hbooks.scaleSize⟩
      · simp only [LedgerController.responseLog, LedgerController.logFor, hr, physicalLedger]
        exact ⟨hbooks.pathSync.entered, hbooks.pathSync.free⟩
      · simp only [LedgerController.responseLog, LedgerController.logFor, hr, physicalLedger]
        exact ⟨hbooks.scaleSync.entered, hbooks.scaleSync.free⟩
    · simp [responsePaths, hr]
    · simp [responseScales, hr]
  | some record =>
    simpa only [responseStreams, responsePaths, responseScales, LedgerController.responseLog,
      LedgerController.logFor, hr] using
      record_accepted threshold hthreshold record ledger (hs.origin record hr) books hbooks

end SortingAdversary.Optimal.ReservationController
