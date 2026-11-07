import SortingAdversary.Optimal.RepairPricing

/-!
# Every emitted hub is an actual physical pin

The chronological hub-vertex list is a sublist of the actual primitive pin
list. This interface transfers the accepted global incidence ledger's
uniqueness of physical promotions to the expensive dictionary history.
-/

namespace SortingAdversary.Optimal.RepairHubPins

open WidthRepair StructuralNormalize RepairPricing

variable {n : ℕ}

def stepPins {s t : State n} : Step s t → List (Fin n)
  | .pin update => [update.vertex]
  | .lowerCut .. => []
  | .upperCut .. => []

def pinVertices {s t : State n} : Trace s t → List (Fin n)
  | .nil _ => []
  | .cons head tail => stepPins head ++ pinVertices tail

theorem pinVertices_append {s t u : State n} (first : Trace s t) (second : Trace t u) :
    pinVertices (first.append second) = pinVertices first ++ pinVertices second := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [Trace.append, pinVertices, ih, List.append_assoc]

def Included {p : Parameters} {s t : State n} {trace : Trace s t} (summary : Summary p trace) : Prop :=
  (summary.hubs.map HubEvent.vertex).Sublist (pinVertices trace)

theorem Included.append {p : Parameters} {s t u : State n} {first : Trace s t} {second : Trace t u}
    {left : Summary p first} {right : Summary p second}
    (hl : Included left) (hr : Included right) : Included (left.append right) := by
  unfold Included at *
  simpa only [Summary.append, List.map_append, pinVertices_append] using hl.append hr

theorem empty_included (p : Parameters) (s : State n) : Included (Summary.empty s p) :=
  List.Sublist.refl _

theorem ordinary_included (p : Parameters) {s : State n} (move : OrdinaryPromotion.Move s) :
    Included (Summary.ordinary p move) := List.Sublist.refl _

theorem early_one_included (p : Parameters) {s : State n} (hB : ComparableBound s p.scale.width.B)
    (move : EarlyMove s p.scale.width.W₀ p.scale.width.L) : Included (Summary.oneEarly p hB move) := by
  cases move <;> exact List.nil_sublist _

theorem early_included (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p.scale.width trace) : Included (Summary.fromEarly p events) := by
  induction events with
  | nil s => exact empty_included p s
  | cons hB move rest events ih => exact (early_one_included p hB move).append ih

theorem scale_included (p : Parameters) (start : State n) (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    {s t : State n} {trace : Trace s t} {indices : List (Fin p.scale.J)}
    (events : ScaleEvents start p.scale trigger normal trace indices) :
    ∀ view : ScaleView start s, Included (Summary.fromScale p start trigger normal events view) := by
  induction events with
  | nil s => intro view; exact empty_included p s
  | cons i update vertex colour interior palette charge rest events ih =>
    intro view
    have hone : Included (Summary.scaleOne p trigger normal view i update vertex colour interior charge) := by
      change [trigger.vertices i].Sublist [update.vertex]
      rw [vertex]
    exact hone.append (ih (view.advance update interior palette))

theorem width_included (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : WidthEvents p.scale trace) : Included (Summary.fromWidth p events) := by
  induction events with
  | early _ events => exact early_included p events
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    exact (early_included p earlyEvents).append
      ((scale_included p _ trigger normal groupEvents (ScaleView.refl _)).append ih)

theorem path_included (p : Parameters) (start : State n) (reservation : Reservation start p.H)
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : Included (Summary.fromPath p start reservation events) := by
  induction events with
  | nil s => exact empty_included p s
  | skip v reserved width widthEvents moved rest events ih => exact (width_included p widthEvents).append ih
  | move v reserved width widthEvents ordinary vertex rest events ih =>
    exact (width_included p widthEvents).append ((ordinary_included p ordinary).append ih)

theorem fromEvents_hubs_sublist (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    ((Summary.fromEvents p events).hubs.map HubEvent.vertex).Sublist (pinVertices trace) := by
  change Included (Summary.fromEvents p events)
  induction events with
  | finish width widthEvents degree => exact width_included p widthEvents
  | degree width widthEvents ordinary selected rest events ih =>
    exact (width_included p widthEvents).append ((ordinary_included p ordinary).append ih)
  | path width widthEvents degree reservation group groupEvents completed rest events ih =>
    exact (width_included p widthEvents).append ((path_included p _ reservation groupEvents).append ih)

end SortingAdversary.Optimal.RepairHubPins
