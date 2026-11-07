import SortingAdversary.Optimal.RepairPricing

/-!
# Every emitted cut consumes one real active row

The cut counter is computed from actual primitive constructors. Pins only
remove rows, and each cut deletes its certified live proper row. The concrete
price summary's cut count is exactly this trace counter.
-/

namespace SortingAdversary.Optimal.RepairPricing

open WidthRepair StructuralNormalize SparseRepairGraph

variable {n : ℕ}

def stepCuts {s t : State n} : Step s t → ℕ
  | .pin _ => 0
  | .lowerCut .. => 1
  | .upperCut .. => 1

def traceCuts {s t : State n} : Trace s t → ℕ
  | .nil _ => 0
  | .cons head rest => stepCuts head + traceCuts rest

theorem traceCuts_append {s t u : State n} (first : Trace s t) (second : Trace t u) :
    traceCuts (first.append second) = traceCuts first + traceCuts second := by
  induction first with
  | nil => simp [Trace.append, traceCuts]
  | cons head rest ih => simp only [Trace.append, traceCuts, ih, Nat.add_assoc]

theorem step_cut_budget {s t : State n} (step : Step s t) :
    stepCuts step + (rawRows t.rows.active).card ≤ (rawRows s.rows.active).card := by
  cases step with
  | pin update =>
    change 0 + (rawRows update.data.rows.active).card ≤ _
    rw [update.data.active_eq, Nat.zero_add]
    exact eraseVertex_count_le s.rows.active update.vertex
  | lowerCut u v live ratio charge retained =>
    have h := eraseRow_count_lt s.rows.active ⟨s.rows.proper u v (s.rows.active_source u v live), live⟩
    rw [State.lowerCut_active]
    change 1 + _ ≤ _
    omega
  | upperCut u v live ratio charge retained =>
    have h := eraseRow_count_lt s.rows.active ⟨s.rows.proper u v (s.rows.active_source u v live), live⟩
    rw [State.upperCut_active]
    change 1 + _ ≤ _
    omega

theorem trace_cut_budget {s t : State n} (trace : Trace s t) :
    traceCuts trace + (rawRows t.rows.active).card ≤ (rawRows s.rows.active).card := by
  induction trace with
  | nil => simp [traceCuts]
  | cons head tail ih =>
    have h := step_cut_budget head
    change stepCuts head + traceCuts tail + _ ≤ _
    omega

namespace Summary

theorem oneEarly_cuts (p : Parameters) {s : State n} (hB : ComparableBound s p.scale.width.B)
    (move : EarlyMove s p.scale.width.W₀ p.scale.width.L) :
    (oneEarly p hB move).cuts = stepCuts (move.execute p.scale.width hB).2 := by
  cases move <;> rfl

theorem fromEarly_cuts (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p.scale.width trace) : (fromEarly p events).cuts = traceCuts trace := by
  induction events with
  | nil => rfl
  | cons hB move rest events ih =>
    change (oneEarly p hB move).cuts + (fromEarly p events).cuts =
      stepCuts (move.execute p.scale.width hB).2 + traceCuts rest
    rw [oneEarly_cuts, ih]

theorem fromScale_cuts (p : Parameters) (start : State n) (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    {s t : State n} {trace : Trace s t} {indices : List (Fin p.scale.J)}
    (events : ScaleEvents start p.scale trigger normal trace indices) :
    ∀ view : ScaleView start s, (fromScale p start trigger normal events view).cuts = traceCuts trace := by
  induction events with
  | nil => intro view; rfl
  | cons i update vertex colour interior palette charge rest events ih =>
    intro view
    simp only [fromScale, append, scaleOne, oneHub, traceCuts, stepCuts, Nat.zero_add, ih]

theorem fromWidth_cuts (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : WidthEvents p.scale trace) : (fromWidth p events).cuts = traceCuts trace := by
  induction events with
  | early trace events => exact fromEarly_cuts p events
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    simp only [fromWidth, append, traceCuts_append, fromEarly_cuts, fromScale_cuts, ih]

theorem fromPath_cuts (p : Parameters) (start : State n) (reservation : Reservation start p.H)
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) :
    (fromPath p start reservation events).cuts = traceCuts trace := by
  induction events with
  | nil => rfl
  | skip v reserved width widthEvents moved rest events ih =>
    simp only [fromPath, append, traceCuts_append, fromWidth_cuts, ih]
  | move v reserved width widthEvents ordinary vertex rest events ih =>
    simp only [fromPath, append, Summary.ordinary, oneHub, traceCuts_append, traceCuts,
      stepCuts, fromWidth_cuts, Nat.zero_add, ih]

theorem fromEvents_cuts (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) : (fromEvents p events).cuts = traceCuts trace := by
  induction events with
  | finish width widthEvents degree => exact fromWidth_cuts p widthEvents
  | degree width widthEvents ordinary selected rest events ih =>
    simp only [fromEvents, append, Summary.ordinary, oneHub, traceCuts_append, traceCuts,
      stepCuts, fromWidth_cuts, Nat.zero_add, ih]
  | path width widthEvents degree reservation group groupEvents completed rest events ih =>
    simp only [fromEvents, append, traceCuts_append, fromWidth_cuts, fromPath_cuts, ih]

/-- The exact local potential inequality used to charge cuts to real physical
source insertions across the whole controller run. -/
theorem fromEvents_cut_budget (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    (fromEvents p events).cuts + (rawRows t.rows.active).card ≤ (rawRows s.rows.active).card := by
  rw [fromEvents_cuts]
  exact trace_cut_budget trace

end Summary
end SortingAdversary.Optimal.RepairPricing
