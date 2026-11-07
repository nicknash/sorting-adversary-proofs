import SortingAdversary.Optimal.ReservationStoredReplay

/-!
# Acceptance and completion of the actual path and scale reservations

Both reservation ledgers remain synchronized with the exact stored-tree
incidence replay. Nested width maintenance consumes a reserved path member
even when that member is moved cheaply or in a scale group.
-/

namespace SortingAdversary.Optimal.ReservationExecution

open WidthRepair LedgerReplayLabels LedgerStoredReplay ReservationAnnotations ReservationStoredReplay
open LedgerTreeBridge LedgerTreeTransitions LedgerSourceHistory LedgerStoredHistory TreeChronology
open ReservationProjection (Book Sync)

variable {n : ℕ}

theorem accepted (threshold : ℕ) (ctx : Context n) (identity : ℕ)
    {H J : ℕ} {pb sb : Bool} {s t : State n} {trace : Trace s t}
    (program : Program H J pb sb trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (hrecorded : Recorded ledger.calls (StoredRepair.node identity s children))
    (E : Fin n → Fin n → Bool) (hsource : RecordedRows ledger.calls identity E)
    (hincident : trace.IncidentFrom E) (hdegree : DegreeLabels threshold trace program.labels)
    (pathBook scaleBook : Book n) (pathSync : Sync pathBook ledger) (scaleSync : Sync scaleBook ledger)
    (pathValid : GroupReservations.Valid pathBook) (scaleValid : GroupReservations.Valid scaleBook)
    (pathIdle : idle pb pathBook) (scaleIdle : idle sb scaleBook) :
    let log := replayLedger identity trace program.labels children hw ho counter ledger
    let actions := streams identity program children hw ho counter
    Nonempty (Outcome pathBook log.ledger actions.path (locations identity program.pathGroups) ×
      Outcome scaleBook log.ledger actions.scale (locations identity program.scaleGroups)) := by
  induction program generalizing children counter ledger pathBook scaleBook with
  | nil => exact ⟨Outcome.nil pathBook ledger pathSync pathValid,
      Outcome.nil scaleBook ledger scaleSync scaleValid⟩
  | @cons pb sb s a t step label tail rest ih =>
    let first := StoredRepair.replayStep identity step children hw ho counter
    let nextLedger := stepLedger identity step label children counter ledger
    have hrun := run_stepActions threshold ctx identity step label children hw counter ha ledger hrep
      E hsource hincident.1 hrecorded.here hdegree.1
    have hnextRep := replayStep_represents ctx identity step label children hw ho counter ha ledger hrep
    have hnextAlloc := replayStep_allocated ctx identity step children hw ho counter ha
    have hnextRecorded : Recorded nextLedger.calls (StoredRepair.node identity a first.children) := by
      rw [stepLedger_calls]
      exact replayStep_recorded identity step children hw ho counter ledger.calls hrecorded
    have hnextSource : RecordedRows nextLedger.calls identity E := by
      rw [stepLedger_calls]
      exact hsource
    let beforePath := Outcome.project threshold _ hrun pathBook pathSync pathValid
    let beforeScale := Outcome.project threshold _ hrun scaleBook scaleSync scaleValid
    obtain ⟨afterPath, afterScale⟩ := ih first.children first.wellFormed first.coherent first.counter
      hnextAlloc nextLedger hnextRep hnextRecorded hnextSource hincident.2 hdegree.2
      beforePath.final beforeScale.final beforePath.sync beforeScale.sync beforePath.valid beforeScale.valid
      (idle_subset pathIdle beforePath.pending) (idle_subset scaleIdle beforeScale.pending)
    exact ⟨beforePath.append afterPath, beforeScale.append afterScale⟩
  | @append pb sb s a t first second before after ih₁ ih₂ =>
    have hi := (incident_append_iff E first second).mp hincident
    have hd := (degree_append_iff threshold first second before.labels after.labels).mp hdegree
    let middle := StoredRepair.replayTrace identity first children hw ho counter
    let beforeLog := replayLedger identity first before.labels children hw ho counter ledger
    have hmiddle := replayLedger_spec threshold ctx identity first before.labels children hw ho counter ha
      ledger hrep hrecorded E hsource hi.1 hd.1
    obtain ⟨firstPath, firstScale⟩ := ih₁ children hw ho counter ha ledger hrep hrecorded hsource hi.1 hd.1
      pathBook scaleBook pathSync scaleSync pathValid scaleValid pathIdle scaleIdle
    have hnextSource : RecordedRows beforeLog.ledger.calls identity E := by
      rw [replayLedger_calls]
      exact hsource
    obtain ⟨lastPath, lastScale⟩ := ih₂ middle.children middle.wellFormed middle.coherent middle.counter
      hmiddle.2.2.1 beforeLog.ledger hmiddle.2.1 hmiddle.2.2.2 hnextSource hi.2 hd.2
      firstPath.final firstScale.final firstPath.sync firstScale.sync firstPath.valid firstScale.valid
      (idle_subset pathIdle firstPath.pending) (idle_subset scaleIdle firstScale.pending)
    dsimp only [Program.labels]
    rw [replayLedger_append]
    simpa only [streams, Program.pathGroups, Program.scaleGroups, locations, List.map_append] using
      (show Nonempty ((Outcome pathBook _ _ _) × (Outcome scaleBook _ _ _)) from
        ⟨firstPath.append lastPath, firstScale.append lastScale⟩)
  | @path sb s t trace members nonempty card free completed body ih =>
    let membersHere := nodeLocations identity members
    have hne : membersHere.Nonempty := Finset.Nonempty.image nonempty _
    have hfree : membersHere ⊆ pathBook.free := by
      intro location hmem
      obtain ⟨hid, hv⟩ := (mem_nodeLocations identity members location).mp hmem
      rcases location with ⟨node, v⟩
      dsimp only at hid hv
      subst node
      rw [pathSync.free]
      exact (local_free ctx identity s children counter ha ledger hrep v).mpr (free hv)
    let reserved : Book n := { pathBook with pending := membersHere, groups := membersHere :: pathBook.groups }
    have hr := ReservationProjection.reserve pathBook membersHere (pathIdle rfl) hne hfree
    have hv : GroupReservations.Valid reserved := GroupReservations.run_valid _ pathValid hr
    have hs : Sync reserved ledger := ⟨pathSync.entered, pathSync.free⟩
    obtain ⟨afterPath, afterScale⟩ := ih children hw ho counter ha ledger hrep hrecorded hsource hincident
      hdegree reserved scaleBook hs scaleSync hv scaleValid (by intro h; cases h) scaleIdle
    let actual := StoredRepair.replayTrace identity trace children hw ho counter
    let log := replayLedger identity trace body.labels children hw ho counter ledger
    have hf := replayLedger_spec threshold ctx identity trace body.labels children hw ho counter ha
      ledger hrep hrecorded E hsource hincident hdegree
    have hdone : ∀ x ∈ membersHere, x ∉ afterPath.final.free := by
      intro location hmem hfree
      obtain ⟨hid, hv⟩ := (mem_nodeLocations identity members location).mp hmem
      rcases location with ⟨node, v⟩
      dsimp only at hid hv
      subst node
      rw [afterPath.sync.free] at hfree
      exact completed v hv ((local_free ctx identity t actual.children actual.counter hf.2.2.1
        log.ledger hf.2.1 v).mp hfree)
    exact ⟨afterPath.reserve membersHere (pathIdle rfl) hne hfree hdone, afterScale⟩
  | @scale pb s t trace members nonempty card free completed body ih =>
    let membersHere := nodeLocations identity members
    have hne : membersHere.Nonempty := Finset.Nonempty.image nonempty _
    have hfree : membersHere ⊆ scaleBook.free := by
      intro location hmem
      obtain ⟨hid, hv⟩ := (mem_nodeLocations identity members location).mp hmem
      rcases location with ⟨node, v⟩
      dsimp only at hid hv
      subst node
      rw [scaleSync.free]
      exact (local_free ctx identity s children counter ha ledger hrep v).mpr (free hv)
    let reserved : Book n := { scaleBook with pending := membersHere, groups := membersHere :: scaleBook.groups }
    have hr := ReservationProjection.reserve scaleBook membersHere (scaleIdle rfl) hne hfree
    have hv : GroupReservations.Valid reserved := GroupReservations.run_valid _ scaleValid hr
    have hs : Sync reserved ledger := ⟨scaleSync.entered, scaleSync.free⟩
    obtain ⟨afterPath, afterScale⟩ := ih children hw ho counter ha ledger hrep hrecorded hsource hincident
      hdegree pathBook reserved pathSync hs pathValid hv pathIdle (by intro h; cases h)
    let actual := StoredRepair.replayTrace identity trace children hw ho counter
    let log := replayLedger identity trace body.labels children hw ho counter ledger
    have hf := replayLedger_spec threshold ctx identity trace body.labels children hw ho counter ha
      ledger hrep hrecorded E hsource hincident hdegree
    have hdone : ∀ x ∈ membersHere, x ∉ afterScale.final.free := by
      intro location hmem hfree
      obtain ⟨hid, hv⟩ := (mem_nodeLocations identity members location).mp hmem
      rcases location with ⟨node, v⟩
      dsimp only at hid hv
      subst node
      rw [afterScale.sync.free] at hfree
      exact completed v hv ((local_free ctx identity t actual.children actual.counter hf.2.2.1
        log.ledger hf.2.1 v).mp hfree)
    exact ⟨afterPath, afterScale.reserve membersHere (scaleIdle rfl) hne hfree hdone⟩

end SortingAdversary.Optimal.ReservationExecution
