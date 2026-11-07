import SortingAdversary.Optimal.ReservationController
import SortingAdversary.Optimal.ControllerRun

/-!
# Actual full controller histories carry completed reservation books

The runner below follows the concrete responses to each query in the actual
history. It emits the incidence actions and both reservation streams, and
records the exact chronological groups selected by those responses.
-/

namespace SortingAdversary.Optimal.ReservationRun

open ReservationMachine ReservationController ReservationStoredReplay
open LedgerTreeBridge LedgerStoredHistory TreeChronology
open RecursiveController ControllerMachine ControllerRun

variable {n : ℕ}

structure Execution (n : ℕ) where
  ledger : IncidenceLedger.State n
  books : Books n
  incidenceActions : List (IncidenceLedger.Action n)
  pathActions : List (GroupReservations.Action (IncidenceLedger.Location n))
  scaleActions : List (GroupReservations.Action (IncidenceLedger.Location n))
  pathGroups : List (Finset (IncidenceLedger.Location n))
  scaleGroups : List (Finset (IncidenceLedger.Location n))

def replay {p : Parameters} (s : Active p n) (observations : History n)
    (ledger : IncidenceLedger.State n) (books : Books n) : Option (Execution n) :=
  match observations with
  | [] => some ⟨ledger, books, [], [], [], [], []⟩
  | observed :: rest => do
      let nextLedger := LedgerController.responseLog s observed.query ledger
      let nextBooks ← ReservationMachine.run books (responseStreams s observed.query)
      let tail ← replay (respond s observed.query).next rest nextLedger.ledger nextBooks
      pure { ledger := tail.ledger, books := tail.books
             incidenceActions := nextLedger.actions ++ tail.incidenceActions
             pathActions := (responseStreams s observed.query).path ++ tail.pathActions
             scaleActions := (responseStreams s observed.query).scale ++ tail.scaleActions
             pathGroups := responsePaths s observed.query ++ tail.pathGroups
             scaleGroups := responseScales s observed.query ++ tail.scaleGroups }

theorem run_some (books after : Books n) (actions : Streams n)
    (h : ReservationMachine.run books actions = some after) :
    GroupReservations.run books.path actions.path = some after.path ∧
      GroupReservations.run books.scale actions.scale = some after.scale := by
  unfold ReservationMachine.run at h
  cases hp : GroupReservations.run books.path actions.path with
  | none => simp [hp] at h
  | some path =>
    cases hs : GroupReservations.run books.scale actions.scale with
    | none => simp [hp, hs] at h
    | some scale =>
      simp only [hp, hs] at h
      change some (Books.mk path scale) = some after at h
      cases h
      exact ⟨rfl, rfl⟩

structure Sound (threshold : ℕ) {p : Parameters} (ledger : IncidenceLedger.State n)
    (books : Books n) (observations : History n) (final : Active p n)
    (execution : Execution n) : Prop where
  incidence : IncidenceLedger.run threshold ledger execution.incidenceActions = some execution.ledger
  paths : GroupReservations.run books.path execution.pathActions = some execution.books.path
  scales : GroupReservations.run books.scale execution.scaleActions = some execution.books.scale
  valid : IncidenceLedger.Valid threshold execution.ledger
  invariant : Invariant p.repair.H p.repair.scale.J execution.books execution.ledger
  represents : Represents execution.ledger final.tree.erase
  allocated : Allocated final.tree.erase final.counter
  recorded : Recorded execution.ledger.calls final.tree
  calls : execution.ledger.calls.length = ledger.calls.length + observations.length
  pathGroups : execution.books.path.groups = execution.pathGroups.reverse ++ books.path.groups
  scaleGroups : execution.books.scale.groups = execution.scaleGroups.reverse ++ books.scale.groups

theorem activeRun_accepted (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    {s final : Active p n} {observations : History n} (history : ActiveRun p s observations final)
    (ledger : IncidenceLedger.State n) (books : Books n)
    (hvalid : IncidenceLedger.Valid threshold ledger)
    (hbooks : Invariant p.repair.H p.repair.scale.J books ledger)
    (halloc : Allocated s.tree.erase s.counter) (hrep : Represents ledger s.tree.erase)
    (hrecorded : Recorded ledger.calls s.tree) :
    ∃ execution : Execution n, replay s observations ledger books = some execution ∧
      Sound threshold ledger books observations final execution := by
  induction history generalizing ledger books with
  | nil s =>
    exact ⟨⟨ledger, books, [], [], [], [], []⟩, rfl,
      ⟨rfl, rfl, rfl, hvalid, hbooks, hrep, halloc, hrecorded, by simp, rfl, rfl⟩⟩
  | @cons s query observations final tail ih =>
    let response := respond s query
    let nextLog := LedgerController.responseLog s query ledger
    let actions := responseStreams s query
    have hs := LedgerController.respond_spec threshold hthreshold s query ledger halloc hrep hrecorded
    obtain ⟨nextBooks, hb, hi, hp, hg⟩ := response_accepted threshold hthreshold s query ledger
      halloc hrep hrecorded books hbooks
    have nextValid : IncidenceLedger.Valid threshold nextLog.ledger :=
      IncidenceLedger.run_valid nextLog.actions hvalid hs.accepted
    obtain ⟨last, hl, hlast⟩ := ih nextLog.ledger nextBooks nextValid hi hs.allocated hs.represents hs.recorded
    let execution : Execution n :=
      ⟨last.ledger, last.books, nextLog.actions ++ last.incidenceActions,
        actions.path ++ last.pathActions, actions.scale ++ last.scaleActions,
        responsePaths s query ++ last.pathGroups, responseScales s query ++ last.scaleGroups⟩
    refine ⟨execution, ?_, ?_⟩
    · dsimp only [replay]
      rw [hb]
      dsimp only [Bind.bind, Option.bind]
      rw [hl]
      rfl
    · have hbs := run_some books nextBooks actions hb
      refine ⟨?_, ?_, ?_, hlast.valid, hlast.invariant, hlast.represents, hlast.allocated,
        hlast.recorded, ?_, ?_, ?_⟩
      · change IncidenceLedger.run threshold ledger (nextLog.actions ++ last.incidenceActions) = _
        have hfirst : IncidenceLedger.run threshold ledger nextLog.actions = some nextLog.ledger := hs.accepted
        rw [LedgerStoredReplay.run_append, hfirst, Option.bind_some, hlast.incidence]
      · change GroupReservations.run books.path (actions.path ++ last.pathActions) = _
        rw [ReservationProjection.run_append, hbs.1, Option.bind_some, hlast.paths]
      · change GroupReservations.run books.scale (actions.scale ++ last.scaleActions) = _
        rw [ReservationProjection.run_append, hbs.2, Option.bind_some, hlast.scales]
      · change last.ledger.calls.length = _
        have hcalls : nextLog.ledger.calls.length = ledger.calls.length + 1 := hs.calls
        rw [hlast.calls, hcalls]
        simp only [List.length_cons]
        omega
      · change last.books.path.groups = _
        rw [hlast.pathGroups, hp]
        simp only [execution, List.reverse_append, List.append_assoc]
      · change last.books.scale.groups = _
        rw [hlast.scaleGroups, hg]
        simp only [execution, List.reverse_append, List.append_assoc]

/-- For a run from the real initial controller state, all ledger and
reservation premises are established here from their concrete initial data. -/
theorem initial_activeRun (p : Parameters) (N : ℕ) {observations : History (N + 2)}
    {final : Active p (N + 2)} (history : ActiveRun p (initialActive p N) observations final) :
    ∃ execution : Execution (N + 2),
      replay (initialActive p N) observations (IncidenceLedger.initial (initialFree (N + 2)))
        (ReservationMachine.initial (initialFree (N + 2))) = some execution ∧
      Sound p.repair.D (IncidenceLedger.initial (initialFree (N + 2)))
        (ReservationMachine.initial (initialFree (N + 2))) observations final execution := by
  apply activeRun_accepted p.repair.D (Nat.le_refl _) history
  · exact IncidenceLedger.initial_valid _ _
  · exact initial_invariant _ _ _
  · simpa only [initialActive, StoredTree.erase_initial] using TreeChronology.initial_allocated N
  · simpa only [initialActive, StoredTree.erase_initial] using initial_represents N
  · exact initial_recorded N

end SortingAdversary.Optimal.ReservationRun
