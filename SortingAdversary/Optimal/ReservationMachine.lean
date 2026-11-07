import SortingAdversary.Optimal.ReservationExecution

/-!
# Concrete completed reservation books for a normalizer result

This runner stores both chronological books. Its input invariant records
completed groups and exact path/scale sizes. The actual normalizer supplies
every new reservation, all child admissions, and all consumption events.
-/

namespace SortingAdversary.Optimal.ReservationMachine

open WidthRepair LedgerReplayLabels LedgerStoredReplay LedgerStructuralReplay
open ReservationAnnotations ReservationStoredReplay
open LedgerTreeBridge LedgerSourceHistory LedgerStoredHistory TreeChronology
open ReservationProjection (Book Sync)

variable {n : ℕ}

structure Books (n : ℕ) where
  path : Book n
  scale : Book n

structure Invariant (H J : ℕ) (books : Books n) (ledger : IncidenceLedger.State n) : Prop where
  pathValid : GroupReservations.Valid books.path
  scaleValid : GroupReservations.Valid books.scale
  pathSync : Sync books.path ledger
  scaleSync : Sync books.scale ledger
  pathDone : books.path.pending = ∅
  scaleDone : books.scale.pending = ∅
  pathSize : ∀ group ∈ books.path.groups, group.card = H
  scaleSize : ∀ group ∈ books.scale.groups, group.card = J

def initial (free : Finset (IncidenceLedger.Location n)) : Books n :=
  ⟨GroupReservations.initial free, GroupReservations.initial free⟩

theorem initial_invariant (H J : ℕ) (free : Finset (IncidenceLedger.Location n)) :
    Invariant H J (initial free) (IncidenceLedger.initial free) := by
  refine ⟨GroupReservations.initial_valid free, GroupReservations.initial_valid free,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_, ?_⟩ <;> simp [initial, GroupReservations.initial]

def run (books : Books n) (actions : Streams n) : Option (Books n) := do
  let path ← GroupReservations.run books.path actions.path
  let scale ← GroupReservations.run books.scale actions.scale
  pure ⟨path, scale⟩

def normalizerStreams (identity : ℕ) {p : StructuralNormalize.Parameters} {s : State n}
    (result : StructuralNormalize.Result s p) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) : Streams n :=
  streams identity (structural result.events) children hw ho counter

def pathGroups (identity : ℕ) {p : StructuralNormalize.Parameters} {s : State n}
    (result : StructuralNormalize.Result s p) : List (Finset (IncidenceLedger.Location n)) :=
  locations identity (structural result.events).pathGroups

def scaleGroups (identity : ℕ) {p : StructuralNormalize.Parameters} {s : State n}
    (result : StructuralNormalize.Result s p) : List (Finset (IncidenceLedger.Location n)) :=
  locations identity (structural result.events).scaleGroups

theorem pathGroups_size (identity : ℕ) {p : StructuralNormalize.Parameters} {s : State n}
    (result : StructuralNormalize.Result s p) :
    ∀ group ∈ pathGroups identity result, group.card = p.H := by
  intro group hg
  obtain ⟨members, hm, rfl⟩ := List.mem_map.mp hg
  rw [nodeLocations_card]
  exact (structural result.events).pathGroups_card members hm

theorem scaleGroups_size (identity : ℕ) {p : StructuralNormalize.Parameters} {s : State n}
    (result : StructuralNormalize.Result s p) :
    ∀ group ∈ scaleGroups identity result, group.card = p.scale.J := by
  intro group hg
  obtain ⟨members, hm, rfl⟩ := List.mem_map.mp hg
  rw [nodeLocations_card]
  exact (structural result.events).scaleGroups_card members hm

theorem recorded_size {before : Book n} {ledger : IncidenceLedger.State n}
    {actions : List (GroupReservations.Action (IncidenceLedger.Location n))}
    {groups : List (Finset (IncidenceLedger.Location n))} (outcome : Outcome before ledger actions groups)
    (size : ℕ) (oldSize : ∀ group ∈ before.groups, group.card = size)
    (newSize : ∀ group ∈ groups, group.card = size) :
    ∀ group ∈ outcome.final.groups, group.card = size := by
  intro group hg
  rw [outcome.recorded] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact newSize group (List.mem_reverse.mp hg)
  · exact oldSize group hg

/-- No acceptance, completion or disjointness premise is required for a new
group: all are derived from the actual normalizer result. -/
theorem normalizer_accepted (threshold : ℕ) (ctx : Context n) (identity : ℕ)
    {p : StructuralNormalize.Parameters} (hthreshold : threshold ≤ p.D) {s : State n}
    (result : StructuralNormalize.Result s p) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (hrecorded : Recorded ledger.calls (StoredRepair.node identity s children))
    (books : Books n) (hbooks : Invariant p.H p.scale.J books ledger) :
    let log := replayLedger identity result.trace (structuralLabels result.events)
      children hw ho counter ledger
    ∃ after : Books n,
      run books (normalizerStreams identity result children hw ho counter) = some after ∧
      Invariant p.H p.scale.J after log.ledger ∧
      after.path.groups = (pathGroups identity result).reverse ++ books.path.groups ∧
      after.scale.groups = (scaleGroups identity result).reverse ++ books.scale.groups := by
  have hdegree : DegreeLabels threshold result.trace (structural result.events).labels := by
    rw [structural_labels]
    exact structuralLabels_degreeLabels threshold hthreshold result.events
  obtain ⟨pathOutcome, scaleOutcome⟩ := ReservationExecution.accepted threshold ctx identity
    (structural result.events) children hw ho counter ha ledger hrep hrecorded s.rows.active
    hrecorded.here result.incident hdegree books.path books.scale hbooks.pathSync hbooks.scaleSync
    hbooks.pathValid hbooks.scaleValid (fun _ => hbooks.pathDone) (fun _ => hbooks.scaleDone)
  refine ⟨⟨pathOutcome.final, scaleOutcome.final⟩, ?_, ?_, pathOutcome.recorded, scaleOutcome.recorded⟩
  · simp only [run, normalizerStreams, pathOutcome.accepted, Option.bind_some,
      scaleOutcome.accepted, pure]
    rfl
  · refine ⟨pathOutcome.valid, scaleOutcome.valid, ?_, ?_, ?_, ?_,
      recorded_size pathOutcome p.H hbooks.pathSize (pathGroups_size identity result),
      recorded_size scaleOutcome p.scale.J hbooks.scaleSize (scaleGroups_size identity result)⟩
    · simpa only [structural_labels] using pathOutcome.sync
    · simpa only [structural_labels] using scaleOutcome.sync
    · exact idle_subset (fun _ => hbooks.pathDone : idle false books.path) pathOutcome.pending rfl
    · exact idle_subset (fun _ => hbooks.scaleDone : idle false books.scale) scaleOutcome.pending rfl

def projected (events : List (IncidenceLedger.Action n)) : Streams n :=
  ⟨ReservationProjection.project events, ReservationProjection.project events⟩

/-- Between reservations, the same real ledger actions update both books.
In particular a known physical query leaves the two books unchanged. -/
theorem projection_accepted (threshold : ℕ) {H J : ℕ} (events : List (IncidenceLedger.Action n))
    {ledger next : IncidenceLedger.State n}
    (h : IncidenceLedger.run threshold ledger events = some next)
    (books : Books n) (hbooks : Invariant H J books ledger) :
    ∃ after : Books n, run books (projected events) = some after ∧ Invariant H J after next ∧
      after.path.groups = books.path.groups ∧ after.scale.groups = books.scale.groups := by
  let po := Outcome.project threshold events h books.path hbooks.pathSync hbooks.pathValid
  let so := Outcome.project threshold events h books.scale hbooks.scaleSync hbooks.scaleValid
  refine ⟨⟨po.final, so.final⟩, ?_, ?_, po.recorded, so.recorded⟩
  · simp only [run, projected, po.accepted, Option.bind_some, so.accepted, pure]
    rfl
  · exact ⟨po.valid, so.valid, po.sync, so.sync,
      idle_subset (fun _ => hbooks.pathDone : idle false books.path) po.pending rfl,
      idle_subset (fun _ => hbooks.scaleDone : idle false books.scale) so.pending rfl,
      recorded_size po H hbooks.pathSize (by simp), recorded_size so J hbooks.scaleSize (by simp)⟩

theorem completed_paths {H J : ℕ} {books : Books n} {ledger : IncidenceLedger.State n}
    (h : Invariant H J books ledger) :
    Pairwise (fun i j : Fin books.path.groups.length =>
      Disjoint (books.path.groups.get i) (books.path.groups.get j)) ∧
      ∀ i : Fin books.path.groups.length, (books.path.groups.get i).card = H ∧
        books.path.groups.get i ⊆ ledger.entered \ ledger.free := by
  refine ⟨GroupReservations.indexed_groups_disjoint h.pathValid, fun i =>
    ⟨h.pathSize _ (List.get_mem _ _), ?_⟩⟩
  simpa only [GroupReservations.consumed, h.pathSync.entered, h.pathSync.free] using
    GroupReservations.completed_group_subset h.pathValid h.pathDone _ (List.get_mem _ _)

theorem completed_scales {H J : ℕ} {books : Books n} {ledger : IncidenceLedger.State n}
    (h : Invariant H J books ledger) :
    Pairwise (fun i j : Fin books.scale.groups.length =>
      Disjoint (books.scale.groups.get i) (books.scale.groups.get j)) ∧
      ∀ i : Fin books.scale.groups.length, (books.scale.groups.get i).card = J ∧
        books.scale.groups.get i ⊆ ledger.entered \ ledger.free := by
  refine ⟨GroupReservations.indexed_groups_disjoint h.scaleValid, fun i =>
    ⟨h.scaleSize _ (List.get_mem _ _), ?_⟩⟩
  simpa only [GroupReservations.consumed, h.scaleSync.entered, h.scaleSync.free] using
    GroupReservations.completed_group_subset h.scaleValid h.scaleDone _ (List.get_mem _ _)

end SortingAdversary.Optimal.ReservationMachine
