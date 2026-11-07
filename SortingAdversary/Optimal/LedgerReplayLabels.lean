import SortingAdversary.Optimal.LedgerSourceHistory
import SortingAdversary.Optimal.WidthScale

/-!
# Ledger classifications from actual normalizer annotations

The width loop's own event constructors determine every physical pin kind.
Cuts carry no pin label. Concatenating the recorded width phases concatenates
their classifications on the very same primitive execution trace.
-/

namespace SortingAdversary.Optimal.LedgerReplayLabels

open WidthRepair
open IncidenceLedger (Kind)

variable {n : ℕ}

def StepLabel {s t : State n} : Step s t → Type
  | .pin _ => Kind
  | .lowerCut .. => PUnit
  | .upperCut .. => PUnit

def Labels {s t : State n} : Trace s t → Type
  | .nil _ => PUnit
  | .cons head tail => StepLabel head × Labels tail

def Labels.append : {s t u : State n} → (first : Trace s t) → (second : Trace t u) →
    Labels first → Labels second → Labels (first.append second)
  | _, _, _, .nil _, _, _, right => right
  | _, _, _, .cons _ tail, second, left, right =>
      (left.1, Labels.append tail second left.2 right)

def StepDegree (threshold : ℕ) {s t : State n} (step : Step s t) : StepLabel step → Prop :=
  match step with
  | .pin update => fun kind => kind = .degree →
      threshold ≤ (GraphBalls.neighbors s.rows.active update.vertex).card
  | .lowerCut .. => fun _ => True
  | .upperCut .. => fun _ => True

def DegreeLabels (threshold : ℕ) {s t : State n} (trace : Trace s t) : Labels trace → Prop :=
  match trace with
  | .nil _ => fun _ => True
  | .cons head tail => fun labels => StepDegree threshold head labels.1 ∧ DegreeLabels threshold tail labels.2

def StepNotDegree {s t : State n} (step : Step s t) : StepLabel step → Prop :=
  match step with
  | .pin _ => fun kind => kind ≠ .degree
  | .lowerCut .. => fun _ => True
  | .upperCut .. => fun _ => True

def NotDegree {s t : State n} (trace : Trace s t) : Labels trace → Prop :=
  match trace with
  | .nil _ => fun _ => True
  | .cons head tail => fun labels => StepNotDegree head labels.1 ∧ NotDegree tail labels.2

theorem notDegree_degreeLabels (threshold : ℕ) {s t : State n} (trace : Trace s t)
    (labels : Labels trace) (h : NotDegree trace labels) : DegreeLabels threshold trace labels := by
  induction trace with
  | nil => trivial
  | cons head tail ih =>
    refine ⟨?_, ih labels.2 h.2⟩
    cases head with
    | pin update => exact fun heq => False.elim (h.1 heq)
    | lowerCut => trivial
    | upperCut => trivial

theorem notDegree_append {s t u : State n} (first : Trace s t) (second : Trace t u)
    (left : Labels first) (right : Labels second) (hl : NotDegree first left)
    (hr : NotDegree second right) : NotDegree (first.append second) (Labels.append first second left right) := by
  induction first with
  | nil => exact hr
  | cons head tail ih => exact ⟨hl.1, ih second left.2 right hl.2 hr⟩

def earlyStepLabel {s : State n} (p : WidthParameters) (hB : ComparableBound s p.B)
    (move : EarlyMove s p.W₀ p.L) : StepLabel (move.execute p hB).2 :=
  match move with
  | .cheap .. => .cheap
  | .lower .. => PUnit.unit
  | .upper .. => PUnit.unit

theorem earlyStepLabel_notDegree {s : State n} (p : WidthParameters) (hB : ComparableBound s p.B)
    (move : EarlyMove s p.W₀ p.L) : StepNotDegree (move.execute p hB).2 (earlyStepLabel p hB move) := by
  cases move with
  | cheap => change Kind.cheap ≠ Kind.degree; decide
  | lower => trivial
  | upper => trivial

def earlyLabels {p : WidthParameters} {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p trace) : Labels trace :=
  match events with
  | .nil _ => PUnit.unit
  | .cons hB move _ events => (earlyStepLabel p hB move, earlyLabels events)

theorem earlyLabels_notDegree {p : WidthParameters} {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p trace) : NotDegree trace (earlyLabels events) := by
  induction events with
  | nil => trivial
  | cons hB move rest events ih => exact ⟨earlyStepLabel_notDegree p hB move, ih⟩

def scaleLabels {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n} {trace : Trace s t}
    {indices : List (Fin p.J)} (events : ScaleEvents start p trigger normal trace indices) : Labels trace :=
  match events with
  | .nil _ => PUnit.unit
  | .cons _ _ _ _ _ _ _ _ events => (Kind.scale, scaleLabels events)

theorem scaleLabels_notDegree {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n} {trace : Trace s t}
    {indices : List (Fin p.J)} (events : ScaleEvents start p trigger normal trace indices) :
    NotDegree trace (scaleLabels events) := by
  induction events with
  | nil => trivial
  | cons _ _ _ _ _ _ _ _ events ih =>
    exact ⟨by change Kind.scale ≠ Kind.degree; decide, ih⟩

def widthLabels {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (events : WidthEvents p trace) : Labels trace :=
  match events with
  | .early _ events => earlyLabels events
  | .scale early earlyEvents _ _ _ group groupEvents rest restEvents =>
      Labels.append early (group.append rest) (earlyLabels earlyEvents)
        (Labels.append group rest (scaleLabels groupEvents) (widthLabels restEvents))

theorem widthLabels_notDegree {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (events : WidthEvents p trace) : NotDegree trace (widthLabels events) := by
  induction events with
  | early trace events => exact earlyLabels_notDegree events
  | scale early earlyEvents _ _ _ group groupEvents rest restEvents ih =>
    exact notDegree_append early (group.append rest) _ _ (earlyLabels_notDegree earlyEvents)
      (notDegree_append group rest _ _ (scaleLabels_notDegree groupEvents) ih)

theorem widthLabels_degreeLabels (threshold : ℕ) {p : ScaleParameters}
    {s t : State n} {trace : Trace s t} (events : WidthEvents p trace) :
    DegreeLabels threshold trace (widthLabels events) :=
  notDegree_degreeLabels threshold trace _ (widthLabels_notDegree events)

end SortingAdversary.Optimal.LedgerReplayLabels
