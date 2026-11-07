import SortingAdversary.Optimal.LedgerStructuralReplay
import SortingAdversary.Optimal.RecursiveController

/-!
# The actual stopping query records one call and its concrete repairs

The payload returned by the recursive controller contains the actual pool,
oriented query, and completed normalizer execution. Its ledger is computed
directly from that payload. Acceptance and the represented tree invariants
follow from the concrete comparison insertion and verified repair replay.
-/

namespace SortingAdversary.Optimal.LedgerQuery

open PoolState WidthRepair PoolTree.Tree TreeChronology LedgerTreeBridge
open LedgerTreeTransitions LedgerSourceHistory LedgerStoredHistory LedgerStoredReplay
open LedgerStructuralReplay RecursiveController

variable {n : ℕ}

def physicalRow {p : Parameters} (record : RepairRecord p n) : Option (IncidenceLedger.Row n) :=
  callRow record.identity record.before.pool record.first record.second

def recordLog {p : Parameters} (record : RepairRecord p n) (ledger : IncidenceLedger.State n) : Log n :=
  let called := physicalLedger ledger (physicalRow record)
  let repair := replayLedger record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter called
  ⟨repair.ledger, .physical (physicalRow record) :: repair.actions⟩

theorem recordLog_calls {p : Parameters} (record : RepairRecord p n) (ledger : IncidenceLedger.State n) :
    (recordLog record ledger).ledger.calls = ledger.calls ++ [physicalRow record] := by
  dsimp only [recordLog]
  rw [replayLedger_calls]
  rfl

theorem recordLog_calls_length {p : Parameters} (record : RepairRecord p n)
    (ledger : IncidenceLedger.State n) :
    (recordLog record ledger).ledger.calls.length = ledger.calls.length + 1 := by
  rw [recordLog_calls]
  simp

theorem recordLog_spec (threshold : ℕ) (ctx : Context n) (p : Parameters)
    (hthreshold : threshold ≤ p.repair.D) (record : RepairRecord p n)
    (ledger : IncidenceLedger.State n)
    (ha : Allocated (ctx.plug (StoredRepair.node record.identity record.before record.children).erase)
      record.counter)
    (hrep : Represents ledger
      (ctx.plug (StoredRepair.node record.identity record.before record.children).erase))
    (hrecorded : Recorded ledger.calls (StoredRepair.node record.identity record.before record.children)) :
    IncidenceLedger.run threshold ledger (recordLog record ledger).actions =
        some (recordLog record ledger).ledger ∧
      Represents (recordLog record ledger).ledger (ctx.plug record.final.erase) ∧
      Allocated (ctx.plug record.final.erase) record.replay.counter ∧
      Recorded (recordLog record ledger).ledger.calls record.final := by
  let after := compared record.before record.first record.second record.first_member record.second_member
    record.distinct record.updated
  let called := physicalLedger ledger (physicalRow record)
  have hrow : IncidenceLedger.rowAdmissible ledger (physicalRow record) :=
    callRow_admissible ledger ctx record.identity record.before.pool (StoredTree.erasedChildren record.children)
      record.first record.second record.distinct (by simpa only [StoredRepair.erase_node] using hrep)
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
  have hs := replay_normalizer_result threshold ctx record.identity after p.repair hthreshold record.result
    record.children record.wellFormed record.coherent record.counter ha' called hrep' hrecorded'
  refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  change IncidenceLedger.run threshold ledger (.physical (physicalRow record) :: _) = _
  rw [IncidenceLedger.run, step_physicalLedger threshold ledger (physicalRow record) hrow, Option.bind_some]
  exact hs.1

/-- The actual stopping site, recovered by the recursive router. -/
def Origin {p : Parameters} (record : RepairRecord p n) (ledger : IncidenceLedger.State n) : Prop :=
  ∃ ctx : Context n,
    Allocated (ctx.plug (StoredRepair.node record.identity record.before record.children).erase) record.counter ∧
    Represents ledger (ctx.plug (StoredRepair.node record.identity record.before record.children).erase) ∧
    Recorded ledger.calls (StoredRepair.node record.identity record.before record.children)

structure Outcome (threshold : ℕ) (ctx : Context n) (p : Parameters)
    (ledger : IncidenceLedger.State n) {t : StoredTree n} {a b : Fin n}
    (answer : StoredRouting.Answered (ready p) (RepairRecord p n) t a b) : Prop where
  accepted : IncidenceLedger.run threshold ledger (recordLog answer.payload ledger).actions =
    some (recordLog answer.payload ledger).ledger
  represents : Represents (recordLog answer.payload ledger).ledger (ctx.plug answer.next.erase)
  allocated : Allocated (ctx.plug answer.next.erase) answer.counter
  recorded : Recorded (recordLog answer.payload ledger).ledger.calls answer.next
  charge : answer.charge = (1 / (1 / 2 - p.error)) * answer.payload.replay.charge
  origin : Origin answer.payload ledger

theorem stop_spec (threshold : ℕ) (ctx : Context n) (p : Parameters)
    (hthreshold : threshold ≤ p.repair.D) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) (counter : ℕ)
    (ledger : IncidenceLedger.State n) (halloc : Allocated (ctx.plug t.erase) counter)
    (hrep : Represents ledger (ctx.plug t.erase)) (hrecorded : Recorded ledger.calls t) :
    Outcome threshold ctx p ledger (RecursiveController.stop p t hw ho normal a b ha hb hab hba hstop counter) := by
  cases t with
  | node identity q d children =>
    let answer := RecursiveController.stop p (.node identity q d children) hw ho normal a b ha hb hab hba hstop counter
    have hs := recordLog_spec threshold ctx p hthreshold answer.payload ledger halloc hrep hrecorded
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rfl, ⟨ctx, halloc, hrep, hrecorded⟩⟩

end SortingAdversary.Optimal.LedgerQuery
