import SortingAdversary.Optimal.LedgerStoredReplay
import SortingAdversary.Optimal.StructuralNormalize

/-!
# Accepted ledger execution for the complete concrete normalizer

The degree selector, reserved-path annotations, and nested width events
determine the actual pin classifications. A degree classification carries
the selected graph degree; every other kind has no degree-charge obligation.
-/

namespace SortingAdversary.Optimal.LedgerStructuralReplay

open WidthRepair StructuralNormalize LedgerReplayLabels LedgerStoredReplay
open LedgerTreeBridge LedgerSourceHistory LedgerStoredHistory TreeChronology
open IncidenceLedger (Kind Row)

variable {n : ℕ}

theorem degreeLabels_append (threshold : ℕ) {s t u : State n}
    (first : Trace s t) (second : Trace t u) (left : Labels first) (right : Labels second)
    (hl : DegreeLabels threshold first left) (hr : DegreeLabels threshold second right) :
    DegreeLabels threshold (first.append second) (Labels.append first second left right) := by
  induction first with
  | nil => exact hr
  | cons head tail ih => exact ⟨hl.1, ih second left.2 right hl.2 hr⟩

def pathLabels {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : Labels trace :=
  match events with
  | .nil _ => PUnit.unit
  | .skip _ _ width widthEvents _ rest events =>
      Labels.append width rest (widthLabels widthEvents) (pathLabels events)
  | .move _ _ width widthEvents ordinary _ rest events =>
      Labels.append width (.cons (.pin ordinary.update) rest) (widthLabels widthEvents)
        (Kind.path, pathLabels events)

theorem pathLabels_notDegree {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : NotDegree trace (pathLabels events) := by
  induction events with
  | nil => trivial
  | skip _ _ width widthEvents _ rest events ih =>
    exact notDegree_append width rest _ _ (widthLabels_notDegree widthEvents) ih
  | move _ _ width widthEvents ordinary _ rest events ih =>
    exact notDegree_append width (.cons (.pin ordinary.update) rest) _ _
      (widthLabels_notDegree widthEvents) ⟨by change Kind.path ≠ Kind.degree; decide, ih⟩

def structuralLabels {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) : Labels trace :=
  match events with
  | .finish _ widthEvents _ => widthLabels widthEvents
  | .degree width widthEvents ordinary _ rest events =>
      Labels.append width (.cons (.pin ordinary.update) rest) (widthLabels widthEvents)
        (Kind.degree, structuralLabels events)
  | .path width widthEvents _ _ group groupEvents _ rest events =>
      Labels.append width (group.append rest) (widthLabels widthEvents)
        (Labels.append group rest (pathLabels groupEvents) (structuralLabels events))

theorem structuralLabels_degreeLabels (threshold : ℕ) {p : Parameters}
    (hthreshold : threshold ≤ p.D) {s t : State n} {trace : Trace s t}
    (events : Events p trace) : DegreeLabels threshold trace (structuralLabels events) := by
  induction events with
  | finish width widthEvents _ => exact widthLabels_degreeLabels threshold widthEvents
  | @degree s a t width widthEvents ordinary selected rest events ih =>
    apply degreeLabels_append threshold width (.cons (.pin ordinary.update) rest) _ _
      (widthLabels_degreeLabels threshold widthEvents)
    refine ⟨?_, ih⟩
    intro _
    exact hthreshold.trans (SparseRepairGraph.degreeWitness_some a.rows.active a.pool.free p.D selected).2
  | path width widthEvents _ _ group groupEvents _ rest events ih =>
    exact degreeLabels_append threshold width (group.append rest) _ _
      (widthLabels_degreeLabels threshold widthEvents)
      (degreeLabels_append threshold group rest _ _
        (notDegree_degreeLabels threshold group _ (pathLabels_notDegree groupEvents)) ih)

/-- The normalizer's actual result now supplies every classification and
incident/degree proof needed by the concrete stored-tree ledger replay. -/
theorem replay_normalizer_result (threshold : ℕ) (ctx : TreeChronology.Context n) (identity : ℕ)
    (s : State n) (p : Parameters) (hthreshold : threshold ≤ p.D) (result : StructuralNormalize.Result s p)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (hrecorded : Recorded ledger.calls (StoredRepair.node identity s children)) :
    let actual := StoredRepair.replayTrace identity result.trace children hw ho counter
    let log := replayLedger identity result.trace (structuralLabels result.events) children hw ho counter ledger
    IncidenceLedger.run threshold ledger log.actions = some log.ledger ∧
      Represents log.ledger (ctx.plug (StoredRepair.node identity result.final actual.children).erase) ∧
      Allocated (ctx.plug (StoredRepair.node identity result.final actual.children).erase) actual.counter ∧
      Recorded log.ledger.calls (StoredRepair.node identity result.final actual.children) :=
  replayLedger_spec threshold ctx identity result.trace (structuralLabels result.events) children hw ho counter ha
    ledger hrep hrecorded s.rows.active hrecorded.here result.incident
      (structuralLabels_degreeLabels threshold hthreshold result.events)

end SortingAdversary.Optimal.LedgerStructuralReplay
