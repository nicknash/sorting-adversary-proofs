import SortingAdversary.Optimal.RepairSignedPrice
import SortingAdversary.Optimal.ReservationAnnotations

/-!
# Exact classifications and reservation counts of emitted hub records

The summary counts agree with the labels on the same primitive trace.
Every scale group emits exactly `J` scale hubs. A path reservation emits at
most `H` ordinary path hubs, since width cleanup can already move some of
its reserved labels.
-/

namespace SortingAdversary.Optimal.RepairEventCounts

open WidthRepair StructuralNormalize RepairPricing LedgerReplayLabels
open LedgerStructuralReplay ReservationAnnotations
open IncidenceLedger (Kind)

instance kindDecidableEq : DecidableEq Kind := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

variable {n : ℕ}

def stepKindCount {s t : State n} (step : Step s t) : StepLabel step → Kind → ℕ :=
  match step with
  | .pin _ => fun (label : Kind) kind => if label = kind then 1 else 0
  | .lowerCut .. => fun _ _ => 0
  | .upperCut .. => fun _ _ => 0

def kindCount : {s t : State n} → (trace : Trace s t) → Labels trace → Kind → ℕ
  | _, _, .nil _, _, _ => 0
  | _, _, .cons head tail, labels, kind =>
      stepKindCount head labels.1 kind + kindCount tail labels.2 kind

theorem kindCount_append {s t u : State n} (first : Trace s t) (second : Trace t u)
    (left : Labels first) (right : Labels second) (kind : Kind) :
    kindCount (first.append second) (Labels.append first second left right) kind =
      kindCount first left kind + kindCount second right kind := by
  induction first with
  | nil => simp [Trace.append, Labels.append, kindCount]
  | cons head tail ih => simp only [Trace.append, Labels.append, kindCount, ih, Nat.add_assoc]

theorem kindCount_append_pin {s a t : State n} (first : Trace s a) (update : PinUpdate a)
    (rest : Trace update.next t) (left : Labels first) (label : Kind) (right : Labels rest)
    (kind : Kind) :
    kindCount (first.append (.cons (.pin update) rest))
      (Labels.append first (.cons (.pin update) rest) left (label, right)) kind =
        kindCount first left kind + (if label = kind then 1 else 0) + kindCount rest right kind := by
  have h := kindCount_append first (.cons (.pin update) rest) left (label, right) kind
  simpa only [kindCount, stepKindCount, Nat.add_assoc] using h

theorem scaleCount_append (first second : List (HubEvent n)) :
    scaleCount (first ++ second) = scaleCount first + scaleCount second := by
  simp [scaleCount, List.filter_append]

structure Recorded {p : Parameters} {s t : State n} {trace : Trace s t}
    (summary : Summary p trace) (labels : Labels trace) : Prop where
  cheap : summary.cheap = kindCount trace labels .cheap
  hubs : summary.hubs.length = kindCount trace labels .degree +
    kindCount trace labels .path + kindCount trace labels .scale
  scale : scaleCount summary.hubs = kindCount trace labels .scale

theorem Recorded.append {p : Parameters} {s t u : State n} {first : Trace s t} {second : Trace t u}
    {left : Summary p first} {right : Summary p second} {a : Labels first} {b : Labels second}
    (ha : Recorded left a) (hb : Recorded right b) :
    Recorded (left.append right) (Labels.append first second a b) := by
  constructor
  · simp only [Summary.append, kindCount_append, ha.cheap, hb.cheap]
  · simp only [Summary.append, List.length_append, kindCount_append, ha.hubs, hb.hubs]
    omega
  · simp only [Summary.append, scaleCount_append, kindCount_append, ha.scale, hb.scale]

theorem empty_recorded (p : Parameters) (s : State n) : Recorded (Summary.empty s p) PUnit.unit := by
  constructor <;> rfl

theorem ordinary_recorded (p : Parameters) {s : State n} (move : OrdinaryPromotion.Move s)
    (kind : Kind) (hk : kind = .degree ∨ kind = .path) :
    Recorded (Summary.ordinary p move) (kind, PUnit.unit) := by
  rcases hk with rfl | rfl <;> constructor <;> rfl

theorem early_one_recorded (p : Parameters) {s : State n}
    (hB : ComparableBound s p.scale.width.B) (move : EarlyMove s p.scale.width.W₀ p.scale.width.L) :
    Recorded (Summary.oneEarly p hB move) (earlyStepLabel p.scale.width hB move, PUnit.unit) := by
  cases move <;> constructor <;> rfl

theorem early_recorded (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p.scale.width trace) : Recorded (Summary.fromEarly p events) (earlyLabels events) := by
  induction events with
  | nil s => exact empty_recorded p s
  | cons hB move rest events ih => exact (early_one_recorded p hB move).append ih

theorem scale_recorded (p : Parameters) (start : State n) (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    {s t : State n} {trace : Trace s t} {indices : List (Fin p.scale.J)}
    (events : ScaleEvents start p.scale trigger normal trace indices) :
    ∀ view : ScaleView start s,
      Recorded (Summary.fromScale p start trigger normal events view) (scaleLabels events) := by
  induction events with
  | nil s => intro view; exact empty_recorded p s
  | cons i update vertex colour interior palette charge rest events ih =>
    intro view
    exact (show Recorded (Summary.scaleOne p trigger normal view i update vertex colour interior charge)
      (Kind.scale, PUnit.unit) from by constructor <;> rfl).append
        (ih (view.advance update interior palette))

theorem width_recorded (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : WidthEvents p.scale trace) : Recorded (Summary.fromWidth p events) (widthLabels events) := by
  induction events with
  | early _ events => exact early_recorded p events
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    exact (early_recorded p earlyEvents).append
      ((scale_recorded p _ trigger normal groupEvents (ScaleView.refl _)).append ih)

theorem path_recorded (p : Parameters) (start : State n) (reservation : Reservation start p.H)
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) :
    Recorded (Summary.fromPath p start reservation events) (pathLabels events) := by
  induction events with
  | nil s => exact empty_recorded p s
  | skip v reserved width widthEvents moved rest events ih => exact (width_recorded p widthEvents).append ih
  | move v reserved width widthEvents ordinary vertex rest events ih =>
    exact (width_recorded p widthEvents).append ((ordinary_recorded p ordinary .path (Or.inr rfl)).append ih)

theorem structural_recorded (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) : Recorded (Summary.fromEvents p events) (structuralLabels events) := by
  induction events with
  | finish width widthEvents degree => exact width_recorded p widthEvents
  | degree width widthEvents ordinary selected rest events ih =>
    exact (width_recorded p widthEvents).append ((ordinary_recorded p ordinary .degree (Or.inl rfl)).append ih)
  | path width widthEvents degree reservation group groupEvents completed rest events ih =>
    exact (width_recorded p widthEvents).append ((path_recorded p _ reservation groupEvents).append ih)

theorem early_other_zero {p : WidthParameters} {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p trace) (kind : Kind) (hk : kind ≠ .cheap) :
    kindCount trace (earlyLabels events) kind = 0 := by
  induction events with
  | nil => rfl
  | cons hB move rest events ih =>
    change stepKindCount (move.execute p hB).2 (earlyStepLabel p hB move) kind +
      kindCount rest (earlyLabels events) kind = 0
    have hone : stepKindCount (move.execute p hB).2 (earlyStepLabel p hB move) kind = 0 := by
      cases move <;> simp [EarlyMove.execute, earlyStepLabel, stepKindCount, Ne.symm hk]
    rw [hone, ih, Nat.zero_add]

theorem scale_kindCount {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n} {trace : Trace s t}
    {indices : List (Fin p.J)} (events : ScaleEvents start p trigger normal trace indices) (kind : Kind) :
    kindCount trace (scaleLabels events) kind = if kind = .scale then indices.length else 0 := by
  induction events with
  | nil => simp [kindCount]
  | cons i update vertex colour interior palette charge rest events ih =>
    cases kind <;> simp [scaleLabels, kindCount, stepKindCount, ih, Nat.add_comm]

theorem width_path_zero {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (events : WidthEvents p trace) : kindCount trace (widthLabels events) .path = 0 := by
  induction events with
  | early _ events => exact early_other_zero events .path (by decide)
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    simp only [widthLabels, kindCount_append, early_other_zero earlyEvents .path (by decide),
      scale_kindCount, ih]
    rfl

theorem plain_paths (H J : ℕ) (pb sb : Bool) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) : (plain H J pb sb trace labels).pathGroups = [] := by
  induction trace with
  | nil => rfl
  | cons head tail ih => exact ih labels.2

theorem plain_scales (H J : ℕ) (pb sb : Bool) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) : (plain H J pb sb trace labels).scaleGroups = [] := by
  induction trace with
  | nil => rfl
  | cons head tail ih => exact ih labels.2

theorem width_paths {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (H : ℕ) (pb : Bool) (events : WidthEvents p trace) : (width H pb events).pathGroups = [] := by
  induction events with
  | early => simp only [width, plain_paths]
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    simp only [width, Program.pathGroups, plain_paths, ih, List.nil_append]

theorem path_paths {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : (path events).pathGroups = [] := by
  induction events with
  | nil => rfl
  | skip _ _ width widthEvents _ rest events ih =>
    simp only [path, Program.pathGroups, width_paths, ih, List.nil_append]
  | move _ _ width widthEvents ordinary _ rest events ih =>
    simp only [path, Program.pathGroups, width_paths, ih, List.nil_append]

theorem width_scale_count {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (H : ℕ) (pb : Bool) (events : WidthEvents p trace) :
    kindCount trace (widthLabels events) .scale = p.J * (width H pb events).scaleGroups.length := by
  induction events with
  | early _ events =>
    simp only [width, plain_scales, List.length_nil, Nat.mul_zero]
    exact early_other_zero events .scale (by decide)
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    simp only [widthLabels, kindCount_append, early_other_zero earlyEvents .scale (by decide),
      scale_kindCount, if_true, List.length_finRange, Nat.zero_add, ih, width,
      Program.scaleGroups, plain_scales, List.nil_append, List.cons_append, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    omega

theorem path_count_le_pending {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) :
    kindCount trace (pathLabels events) .path ≤ pending.length := by
  induction events with
  | nil => exact Nat.zero_le _
  | skip _ _ width widthEvents _ rest events ih =>
    simp only [pathLabels, kindCount_append, width_path_zero, Nat.zero_add, List.length_cons]
    omega
  | move _ _ width widthEvents ordinary _ rest events ih =>
    simp only [pathLabels, kindCount_append_pin, width_path_zero, Nat.zero_add,
      if_true, List.length_cons]
    omega

theorem path_scale_count {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) :
    kindCount trace (pathLabels events) .scale = p.scale.J * (path events).scaleGroups.length := by
  induction events with
  | nil => simp [kindCount, path, Program.scaleGroups]
  | skip _ _ width widthEvents _ rest events ih =>
    simp only [pathLabels, kindCount_append, width_scale_count p.H true widthEvents,
      ih, path, Program.scaleGroups, List.length_append, Nat.mul_add]
  | move _ _ width widthEvents ordinary _ rest events ih =>
    simp only [pathLabels, kindCount_append_pin, width_scale_count p.H true widthEvents,
      reduceCtorEq, if_false, Nat.add_zero,
      ih, path, Program.scaleGroups, List.length_append, Nat.mul_add]

theorem structural_path_count {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    kindCount trace (structuralLabels events) .path ≤ p.H * (structural events).pathGroups.length := by
  induction events with
  | finish width widthEvents degree =>
    simp only [structuralLabels, width_path_zero, structural, width_paths, List.length_nil, Nat.mul_zero]
    exact le_rfl
  | degree width widthEvents ordinary selected rest events ih =>
    simpa only [structuralLabels, kindCount_append_pin, width_path_zero, Nat.zero_add,
      reduceCtorEq, if_false, structural, Program.pathGroups, width_paths,
      List.nil_append] using ih
  | path width widthEvents degree reservation group groupEvents completed rest events ih =>
    have hg := path_count_le_pending groupEvents
    rw [reservation.length] at hg
    simp only [structuralLabels, kindCount_append, width_path_zero, Nat.zero_add,
      structural, Program.pathGroups, width_paths, path_paths, List.nil_append, List.cons_append,
      List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem structural_scale_count {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    kindCount trace (structuralLabels events) .scale = p.scale.J * (structural events).scaleGroups.length := by
  induction events with
  | finish width widthEvents degree => exact width_scale_count p.H false widthEvents
  | degree width widthEvents ordinary selected rest events ih =>
    simp only [structuralLabels, kindCount_append_pin, width_scale_count p.H false widthEvents,
      reduceCtorEq, if_false, Nat.add_zero,
      ih, structural, Program.scaleGroups, List.length_append, Nat.mul_add]
  | path width widthEvents degree reservation group groupEvents completed rest events ih =>
    simp only [structuralLabels, kindCount_append, width_scale_count p.H false widthEvents,
      path_scale_count, ih, structural, Program.scaleGroups, List.length_append, Nat.mul_add]

theorem actual_scale_count (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    scaleCount (Summary.fromEvents p events).hubs = p.scale.J * (structural events).scaleGroups.length := by
  rw [(structural_recorded p events).scale, structural_scale_count]

theorem actual_hub_count (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    (Summary.fromEvents p events).hubs.length ≤
      kindCount trace (structuralLabels events) .degree +
        p.H * (structural events).pathGroups.length +
        p.scale.J * (structural events).scaleGroups.length := by
  rw [(structural_recorded p events).hubs, structural_scale_count]
  exact Nat.add_le_add_right (Nat.add_le_add_left (structural_path_count events) _) _

end SortingAdversary.Optimal.RepairEventCounts
