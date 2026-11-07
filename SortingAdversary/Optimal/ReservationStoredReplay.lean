import SortingAdversary.Optimal.ReservationAnnotations

/-!
# Two reservation streams from the actual stored-tree replay

The two streams use the exact promotions, receiving child identities and
admissions computed by `StoredRepair`. Reservation markers are inserted only
at the boundaries extracted from the concrete normalizer's own events.
-/

namespace SortingAdversary.Optimal.ReservationStoredReplay

open WidthRepair LedgerReplayLabels LedgerStoredReplay ReservationAnnotations
open LedgerTreeBridge LedgerTreeTransitions LedgerSourceHistory LedgerStoredHistory TreeChronology
open ReservationProjection (Book Sync)

variable {n : ℕ}

theorem replayTrace_append (identity : ℕ) {s a t : State n}
    (first : Trace s a) (second : Trace a t) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    let initial := StoredRepair.replayTrace identity first children hw ho counter
    let tail := StoredRepair.replayTrace identity second initial.children initial.wellFormed
      initial.coherent initial.counter
    (StoredRepair.replayTrace identity (first.append second) children hw ho counter).children =
        tail.children ∧
      (StoredRepair.replayTrace identity (first.append second) children hw ho counter).counter =
        tail.counter := by
  induction first generalizing children counter with
  | nil => exact ⟨rfl, rfl⟩
  | cons head rest ih =>
    dsimp only [Trace.append, StoredRepair.replayTrace]
    exact ih second _ _ _ _

theorem replayLedger_append (identity : ℕ) {s a t : State n}
    (first : Trace s a) (second : Trace a t) (left : Labels first) (right : Labels second)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ledger : IncidenceLedger.State n) :
    let initial := StoredRepair.replayTrace identity first children hw ho counter
    let before := replayLedger identity first left children hw ho counter ledger
    let after := replayLedger identity second right initial.children initial.wellFormed
      initial.coherent initial.counter before.ledger
    replayLedger identity (first.append second) (Labels.append first second left right)
      children hw ho counter ledger = ⟨after.ledger, before.actions ++ after.actions⟩ := by
  induction first generalizing children counter ledger with
  | nil => rfl
  | cons head rest ih =>
    dsimp only [Trace.append, Labels.append, replayLedger, StoredRepair.replayTrace]
    rw [ih]
    simp only [List.append_assoc]

theorem incident_append_iff (E : Fin n → Fin n → Bool) {s a t : State n}
    (first : Trace s a) (second : Trace a t) :
    (first.append second).IncidentFrom E ↔ first.IncidentFrom E ∧ second.IncidentFrom E := by
  induction first with
  | nil => simp [Trace.IncidentFrom, Trace.append]
  | cons head rest ih =>
    simp only [Trace.IncidentFrom, Trace.append, ih, and_assoc]

theorem degree_append_iff (threshold : ℕ) {s a t : State n}
    (first : Trace s a) (second : Trace a t) (left : Labels first) (right : Labels second) :
    DegreeLabels threshold (first.append second) (Labels.append first second left right) ↔
      DegreeLabels threshold first left ∧ DegreeLabels threshold second right := by
  induction first with
  | nil => simp [DegreeLabels, Trace.append, Labels.append]
  | cons head rest ih =>
    simp only [DegreeLabels, Trace.append, Labels.append, ih, and_assoc]

def idle (busy : Bool) (book : Book n) : Prop := busy = false → book.pending = ∅

theorem idle_subset {busy : Bool} {before after : Book n} (h : idle busy before)
    (hp : after.pending ⊆ before.pending) : idle busy after := by
  intro hb
  exact Finset.eq_empty_iff_forall_notMem.mpr (by
    intro x hx
    have := hp hx
    simpa [h hb] using this)

structure Streams (n : ℕ) where
  path : List (GroupReservations.Action (IncidenceLedger.Location n))
  scale : List (GroupReservations.Action (IncidenceLedger.Location n))

def streams (identity : ℕ) {H J : ℕ} {pb sb : Bool} {s t : State n}
    {trace : Trace s t} (program : Program H J pb sb trace)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) : Streams n :=
  match program with
  | .nil .. => ⟨[], []⟩
  | .cons step label _ rest =>
      let first := StoredRepair.replayStep identity step children hw ho counter
      let after := streams identity rest first.children first.wellFormed first.coherent first.counter
      let projected := ReservationProjection.project (stepActions identity step label children counter)
      ⟨projected ++ after.path, projected ++ after.scale⟩
  | .append first _ before after =>
      let middle := StoredRepair.replayTrace identity first children hw ho counter
      let left := streams identity before children hw ho counter
      let right := streams identity after middle.children middle.wellFormed middle.coherent middle.counter
      ⟨left.path ++ right.path, left.scale ++ right.scale⟩
  | .path _ members _ _ _ _ body =>
      let after := streams identity body children hw ho counter
      ⟨.reserve (nodeLocations identity members) :: after.path, after.scale⟩
  | .scale _ members _ _ _ _ body =>
      let after := streams identity body children hw ho counter
      ⟨after.path, .reserve (nodeLocations identity members) :: after.scale⟩

def locations (identity : ℕ) (groups : List (Finset (Fin n))) :
    List (Finset (IncidenceLedger.Location n)) := groups.map (nodeLocations identity)

structure Outcome (before : Book n) (ledger : IncidenceLedger.State n)
    (actions : List (GroupReservations.Action (IncidenceLedger.Location n)))
    (groups : List (Finset (IncidenceLedger.Location n))) where
  final : Book n
  accepted : GroupReservations.run before actions = some final
  sync : Sync final ledger
  valid : GroupReservations.Valid final
  pending : final.pending ⊆ before.pending
  recorded : final.groups = groups.reverse ++ before.groups

def Outcome.nil (book : Book n) (ledger : IncidenceLedger.State n)
    (hs : Sync book ledger) (hv : GroupReservations.Valid book) : Outcome book ledger [] [] :=
  ⟨book, rfl, hs, hv, Finset.Subset.refl _, rfl⟩

def Outcome.append {before : Book n} {ledger₁ ledger₂ : IncidenceLedger.State n}
    {a b : List (GroupReservations.Action (IncidenceLedger.Location n))}
    {g h : List (Finset (IncidenceLedger.Location n))}
    (left : Outcome before ledger₁ a g) (right : Outcome left.final ledger₂ b h) :
    Outcome before ledger₂ (a ++ b) (g ++ h) where
  final := right.final
  accepted := by rw [ReservationProjection.run_append, left.accepted, Option.bind_some, right.accepted]
  sync := right.sync
  valid := right.valid
  pending := right.pending.trans left.pending
  recorded := by rw [right.recorded, left.recorded, List.reverse_append, List.append_assoc]

def Outcome.project (threshold : ℕ) (events : List (IncidenceLedger.Action n))
    {ledger next : IncidenceLedger.State n}
    (h : IncidenceLedger.run threshold ledger events = some next)
    (book : Book n) (hs : Sync book ledger) (hv : GroupReservations.Valid book) :
    Outcome book next (ReservationProjection.project events) [] := by
  have hex := ReservationProjection.run threshold events h book hs
  cases ha : GroupReservations.run book (ReservationProjection.project events) with
  | none =>
      apply False.elim
      obtain ⟨after, he, _⟩ := hex
      rw [ha] at he
      contradiction
  | some after =>
      refine ⟨after, ha, ?_, GroupReservations.run_valid _ hv ha, ?_, ?_⟩
      all_goals
        obtain ⟨last, he, hsync, hp, hg⟩ := hex
        rw [ha] at he
        cases he
      · exact hsync
      · exact hp
      · exact hg

def Outcome.reserve {before : Book n} {next : IncidenceLedger.State n}
    {actions : List (GroupReservations.Action (IncidenceLedger.Location n))}
    {groups : List (Finset (IncidenceLedger.Location n))}
    (members : Finset (IncidenceLedger.Location n)) (hempty : before.pending = ∅)
    (hne : members.Nonempty) (hfree : members ⊆ before.free)
    (after : Outcome { before with pending := members, groups := members :: before.groups }
      next actions groups)
    (hdone : ∀ x ∈ members, x ∉ after.final.free) :
    Outcome before next (.reserve members :: actions) (members :: groups) where
  final := after.final
  accepted := by
    change GroupReservations.run before ([.reserve members] ++ actions) = _
    rw [ReservationProjection.run_append, ReservationProjection.reserve before members hempty hne hfree,
      Option.bind_some, after.accepted]
  sync := after.sync
  valid := after.valid
  pending := by
    have hz := ReservationProjection.pending_empty after.valid members after.pending hdone
    simp only [hz, Finset.empty_subset]
  recorded := by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using after.recorded

theorem local_free (ctx : Context n) (identity : ℕ) (s : State n)
    (children : List (ℕ × StoredTree n)) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (v : Fin n) : (identity, v) ∈ ledger.free ↔ v ∈ s.pool.free := by
  rw [hrep.free]
  apply treeLocations_at_identity ha (identity, s.pool)
  apply storedPools_mem_plug ctx
  rw [StoredRepair.erase_node, PoolTreeTraversal.storedPools]
  exact List.mem_cons_self

end SortingAdversary.Optimal.ReservationStoredReplay
