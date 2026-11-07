import SortingAdversary.Optimal.WidthInterior

/-!
# Executing the complete width-normalization loop

Reserved scale labels are pinned in their actual chronological hub order.
Every pending label retains its original effective window, so all point-mass
prices refer to the current parent law. The global loop always finishes the
reserved group before testing the next width violation.
-/

namespace SortingAdversary.Optimal.WidthRepair

open WeakMaps WeakMaps.WeakSystem FiniteInsertion NumericalRepresentation SparseClosure
open GraphBalls PoolState FiniteRefinement PinTransitions SeparatedPins ScaleMass

variable {n : ℕ}

/-- Proof-only state of a reserved scale group. The actual current pool is
the input; no numerical law or conclusion is supplied by an external oracle. -/
structure ScaleContext (start current : State n) (p : ScaleParameters)
    (trigger : ScaleTrigger start p) (pending : List (Fin p.J)) : Prop where
  activeOld : ∀ x y, current.rows.active x y = true → start.rows.active x y = true
  publicEq : current.pool.system.edge = start.pool.system.edge
  membersEq : current.pool.members = start.pool.members
  paletteEq : current.pool.palette = start.pool.palette
  orderEq : HEq current.order start.order
  bound : ComparableBound current p.width.B
  free : ∀ i ∈ pending, current.pool.pins (trigger.vertices i) = none
  lower : ∀ i ∈ pending, (current.pool.system.effectiveLower (trigger.vertices i)).val =
    (start.pool.system.effectiveLower (trigger.vertices i)).val
  upper : ∀ i ∈ pending, (current.pool.system.effectiveUpper (trigger.vertices i)).val =
    (start.pool.system.effectiveUpper (trigger.vertices i)).val

namespace ScaleContext

variable {start current : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
variable {pending : List (Fin p.J)}

def colour (context : ScaleContext start current p trigger pending)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (i : Fin p.J) : Fin (current.pool.palette + 1) :=
  ⟨(trigger.colour normal i).val, by rw [context.paletteEq]; exact (trigger.colour normal i).isLt⟩

theorem interior (context : ScaleContext start current p trigger pending)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (i : Fin p.J) (hi : i ∈ pending) :
    current.pool.system.effectiveLower (trigger.vertices i) < context.colour normal i ∧
      context.colour normal i < current.pool.system.effectiveUpper (trigger.vertices i) := by
  have h := trigger.colour_interior normal i
  change (current.pool.system.effectiveLower _).val < (trigger.colour normal i).val ∧
    (trigger.colour normal i).val < (current.pool.system.effectiveUpper _).val
  rw [context.lower i hi, context.upper i hi]
  exact h

theorem central_eq (context : ScaleContext start current p trigger pending)
    (i : Fin p.J) (hi : i ∈ pending) :
    intervalLower current.numerical (trigger.vertices i) = intervalLower start.numerical (trigger.vertices i) ∧
      intervalUpper current.numerical (trigger.vertices i) = intervalUpper start.numerical (trigger.vertices i) := by
  have hc := current.numerical_windows (trigger.vertices i)
  have hs := start.numerical_windows (trigger.vertices i)
  simp only [intervalLower, intervalUpper, hc.1, hc.2, hs.1, hs.2, context.lower i hi, context.upper i hi]
  exact ⟨trivial, trivial⟩

theorem charge (context : ScaleContext start current p trigger pending)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (i : Fin p.J) (hi : i ∈ pending) :
    (current.pool.system.count : ℚ) ≤
      (2 * 4 ^ p.width.B * (trigger.upper i.val - trigger.lower i.val) : ℕ) *
        (pinAt current.pool.system (trigger.vertices i) (context.colour normal i)).count := by
  have hmem : intervalLower current.numerical (trigger.vertices i) ≤ (context.colour normal i).val ∧
      (context.colour normal i).val < intervalUpper current.numerical (trigger.vertices i) := by
    rw [(context.central_eq i hi).1, (context.central_eq i hi).2]
    exact trigger.colour_mem normal i
  have h := central_count_by_length current.numerical current.numerical_feasible (trigger.vertices i)
    (context.colour normal i) p.width.B (context.bound _) hmem
  rw [current.numerical_count, current.numerical_fiber,
    (context.central_eq i hi).1, (context.central_eq i hi).2] at h
  simp only [ScaleTrigger.upper_fin, ScaleTrigger.lower_fin, count, maps_pinAt]
  exact_mod_cast h

def update (context : ScaleContext start current p trigger pending)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (i : Fin p.J) (hi : i ∈ pending) : PinUpdate current :=
  current.interiorUpdate (trigger.vertices i) (context.free i hi) (context.colour normal i)
    (context.interior normal i hi)
    (hasMate_of_same_public context.membersEq context.publicEq
      (start.nonisolated_mate (trigger.vertices_incident normal i)))
    (2 * 4 ^ p.width.B * (trigger.upper i.val - trigger.lower i.val) : ℕ)
    (context.charge normal i hi)

theorem advance {i : Fin p.J} {rest : List (Fin p.J)}
    (context : ScaleContext start current p trigger (i :: rest))
    (normal : EarlyNormal start p.width.W₀ p.width.L) {d : ℕ}
    (g : LocalOracle.SparseBounds start.rows p.H d) (hnd : (i :: rest).Nodup) :
    ScaleContext start (context.update normal i (List.mem_cons_self ..)).next p trigger rest where
  activeOld x y h := context.activeOld x y ((Step.pin (context.update normal i (List.mem_cons_self ..))).active_old x y h)
  publicEq := context.publicEq
  membersEq := context.membersEq
  paletteEq := context.paletteEq
  orderEq := context.orderEq
  bound := comparableBound_step (.pin (context.update normal i (List.mem_cons_self ..))) context.bound
  free := by
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact (List.nodup_cons.mp hnd).1 hj
    have hv : trigger.vertices j ≠ trigger.vertices i := fun h => hji (trigger.vertices_injective normal h)
    change recordPin current.pool.pins (trigger.vertices i) (context.colour normal i) (trigger.vertices j) = none
    simp [recordPin, hv, context.free j (List.mem_cons_of_mem i hj)]
  lower := by
    intro j hj
    have hij : i ≠ j := by intro h; subst j; exact (List.nodup_cons.mp hnd).1 hj
    have hinc := trigger.vertices_incomparable normal g hij
    have hw := current.pin_windows_unchanged (trigger.vertices i) (trigger.vertices j)
      (context.colour normal i) ⟨(context.interior normal i (List.mem_cons_self ..)).1.le,
        (context.interior normal i (List.mem_cons_self ..)).2.le⟩
      (numerical_incomparable_of_subset context.activeOld hinc.1)
      (numerical_incomparable_of_subset context.activeOld hinc.2)
    exact (congrArg Fin.val hw.1).trans (context.lower j (List.mem_cons_of_mem i hj))
  upper := by
    intro j hj
    have hij : i ≠ j := by intro h; subst j; exact (List.nodup_cons.mp hnd).1 hj
    have hinc := trigger.vertices_incomparable normal g hij
    have hw := current.pin_windows_unchanged (trigger.vertices i) (trigger.vertices j)
      (context.colour normal i) ⟨(context.interior normal i (List.mem_cons_self ..)).1.le,
        (context.interior normal i (List.mem_cons_self ..)).2.le⟩
      (numerical_incomparable_of_subset context.activeOld hinc.1)
      (numerical_incomparable_of_subset context.activeOld hinc.2)
    exact (congrArg Fin.val hw.2).trans (context.upper j (List.mem_cons_of_mem i hj))

end ScaleContext

/-- Each annotation ties the actual physical pin to its reserved label,
immutable hub block, precise palette rank, and true-parent count charge. -/
inductive ScaleEvents (start : State n) (p : ScaleParameters) (trigger : ScaleTrigger start p)
    (normal : EarlyNormal start p.width.W₀ p.width.L) :
    {s t : State n} → Trace s t → List (Fin p.J) → Type
  | nil (s : State n) : ScaleEvents start p trigger normal (.nil s) []
  | cons {s t : State n} (i : Fin p.J) (update : PinUpdate s)
      (vertex : update.vertex = trigger.vertices i)
      (colour : update.colour.val = (trigger.colour normal i).val)
      (interior : s.pool.system.effectiveLower update.vertex < update.colour ∧
        update.colour < s.pool.system.effectiveUpper update.vertex)
      (palette : update.result.palette = s.pool.palette)
      (charge : update.charge = (2 * 4 ^ p.width.B * (trigger.upper i.val - trigger.lower i.val) : ℕ))
      (rest : Trace update.next t) {indices : List (Fin p.J)}
      (events : ScaleEvents start p trigger normal rest indices) :
      ScaleEvents start p trigger normal (.cons (.pin update) rest) (i :: indices)

theorem ScaleEvents.free_card {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n} {trace : Trace s t}
    {indices : List (Fin p.J)} (events : ScaleEvents start p trigger normal trace indices) :
    t.pool.free.card + indices.length = s.pool.free.card := by
  induction events with
  | nil s => simp
  | @cons s t i update _ _ _ _ _ rest indices events ih =>
    have h := Pool.installPromotion_free_card s.pool update.vertex update.free update.colour update.result
    change update.next.pool.free.card + 1 = s.pool.free.card at h
    simp only [List.length_cons]
    omega

structure ScaleRunResult (start current : State n) (p : ScaleParameters) (trigger : ScaleTrigger start p)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (pending : List (Fin p.J)) where
  final : State n
  trace : Trace current final
  events : ScaleEvents start p trigger normal trace pending
  incident : trace.IncidentFrom start.rows.active
  length : trace.length = pending.length
  bound : ComparableBound final p.width.B
  palette : final.pool.palette = current.pool.palette
  order : HEq final.order current.order

def runScaleAux (start current : State n) (p : ScaleParameters) (trigger : ScaleTrigger start p)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (d : ℕ)
    (g : LocalOracle.SparseBounds start.rows p.H d) (pending : List (Fin p.J))
    (hnd : pending.Nodup) (context : ScaleContext start current p trigger pending) :
    ScaleRunResult start current p trigger normal pending :=
  match pending with
  | [] => ⟨current, .nil current, .nil current, trivial, rfl, context.bound, rfl, HEq.rfl⟩
  | i :: rest =>
    let update := context.update normal i (List.mem_cons_self ..)
    let tail := runScaleAux start update.next p trigger normal d g rest hnd.of_cons
      (context.advance normal g hnd)
    ⟨tail.final, .cons (.pin update) tail.trace,
      .cons i update rfl rfl (context.interior normal i (List.mem_cons_self ..)) rfl rfl tail.trace tail.events,
      ⟨trigger.vertices_incident normal i, tail.incident⟩,
      by change tail.trace.length + 1 = rest.length + 1; rw [tail.length],
      tail.bound, tail.palette, tail.order⟩

def executeScale (s : State n) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    ScaleRunResult s s p trigger normal (List.finRange p.J) :=
  runScaleAux s s p trigger normal d g (List.finRange p.J) (List.nodup_finRange _) {
    activeOld := fun _ _ h => h
    publicEq := rfl
    membersEq := rfl
    paletteEq := rfl
    orderEq := HEq.rfl
    bound := hB
    free := fun i _ => s.nonisolated_free (trigger.vertices_incident normal i)
    lower := fun _ _ => rfl
    upper := fun _ _ => rfl }

theorem executeScale_length (s : State n) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (executeScale s p trigger normal d g hB).trace.length = p.J := by
  simpa only [List.length_finRange] using (executeScale s p trigger normal d g hB).length

theorem executeScale_measure_lt (s : State n) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (executeScale s p trigger normal d g hB).final.measure < s.measure := by
  have h := (executeScale s p trigger normal d g hB).trace.length_add_measure_le
  rw [executeScale_length] at h
  have hJ := p.J_pos
  omega

theorem executeScale_free_card (s : State n) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (executeScale s p trigger normal d g hB).final.pool.free.card + p.J = s.pool.free.card := by
  simpa only [List.length_finRange] using (executeScale s p trigger normal d g hB).events.free_card

/-- All three terminal width conditions, on the actual final active graph. -/
structure WidthNormal (s : State n) (p : ScaleParameters) : Prop extends EarlyNormal s p.width.W₀ p.width.L where
  component : ∀ x y, Connected s.rows.active x y → s.width y ≤ p.R * s.width x

/-- The completed width loop supplies the local oracle's real mark premise.
There is no connected-component condition left for the caller to assume. -/
theorem WidthNormal.markCondition {s : State n} {p : ScaleParameters} (normal : WidthNormal s p)
    (d : ℕ) (ε : ℚ)
    (hminimum : LocalParameters.minimumWidth p.H (LocalAccuracy.influenceSize p.H d) p.R ε ≤ p.width.W₀)
    (x : Fin n) : IsolatedAccuracy.MarkCondition s.rows.view p.H d p.R ε x := by
  apply LocalOracle.markCondition_of_widths s.rows s.pool.pin_bounds s.pool.invariant.feasible p.H d p.R ε x
  by_cases hiso : neighbors s.rows.active x = ∅
  · exact Or.inl ((IsolatedCoupling.isolated_iff_neighbors_empty _ _).mpr hiso)
  · refine Or.inr ⟨?_, ?_⟩
    · intro y hy
      exact_mod_cast normal.component x y hy
    · have hw := normal.wide x (Finset.nonempty_iff_ne_empty.mpr hiso)
      exact_mod_cast hminimum.trans hw

/-- A completed scale group has one reservation start, all its chronological
physical pins, and one completion. Early cheap pins and cuts retain their
own constructors, so downstream accounting never infers a kind from a cost. -/
inductive WidthEvents (p : ScaleParameters) : {s t : State n} → Trace s t → Type
  | early {s t : State n} (trace : Trace s t) (events : EarlyEvents p.width trace) : WidthEvents p trace
  | scale {s a b t : State n} (early : Trace s a) (earlyEvents : EarlyEvents p.width early)
      (trigger : ScaleTrigger a p) (selected : selectScale a p = some trigger)
      (normal : EarlyNormal a p.width.W₀ p.width.L)
      (group : Trace a b) (groupEvents : ScaleEvents a p trigger normal group (List.finRange p.J))
      (rest : Trace b t) (restEvents : WidthEvents p rest) :
      WidthEvents p (early.append (group.append rest))

structure WidthResult (s : State n) (p : ScaleParameters) where
  final : State n
  trace : Trace s final
  events : WidthEvents p trace
  incident : trace.IncidentFrom s.rows.active
  bound : ComparableBound final p.width.B
  normal : WidthNormal final p

/-- The concrete complete loop: normalize W1/W2, reserve and finish a W3
group if the materialized pair scan finds one, and repeat. -/
def normalizeWidths (s : State n) (p : ScaleParameters) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) : WidthResult s p :=
  let early := normalizeEarly s p.width hB
  match selected : selectScale early.final p with
  | none =>
    ⟨early.final, early.trace, .early early.trace early.events, early.incident, early.bound,
      { toEarlyNormal := early.normal, component := (selectScale_none early.final p).mp selected }⟩
  | some trigger =>
    let group := executeScale early.final p trigger early.normal d (early.trace.sparseBounds g) early.bound
    let rest := normalizeWidths group.final p d ((early.trace.append group.trace).sparseBounds g) group.bound
    ⟨rest.final, early.trace.append (group.trace.append rest.trace),
      .scale early.trace early.events trigger selected early.normal group.trace group.events rest.trace rest.events,
      early.trace.incidentFrom_append (group.trace.append rest.trace) early.incident
        (group.trace.incidentFrom_append rest.trace
          (group.trace.incidentFrom_mono early.trace.active_old group.incident)
          (rest.trace.incidentFrom_mono (early.trace.append group.trace).active_old rest.incident)),
      rest.bound, rest.normal⟩
termination_by s.measure
decreasing_by
  have hg := executeScale_measure_lt early.final p trigger early.normal d (early.trace.sparseBounds g) early.bound
  have he := early.trace.length_add_measure_le
  exact hg.trans_le (by omega)

theorem normalizeWidths_steps_le (s : State n) (p : ScaleParameters) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (normalizeWidths s p d g hB).trace.length ≤
      s.pool.free.card + (SparseRepairGraph.rawRows s.rows.active).card := by
  have h := (normalizeWidths s p d g hB).trace.length_add_measure_le
  exact (Nat.le_add_right _ _).trans h

theorem normalizeWidths_steps_le_quadratic (s : State n) (p : ScaleParameters) (d : ℕ)
    (g : LocalOracle.SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (normalizeWidths s p d g hB).trace.length ≤ n + n * n := by
  have hf : s.pool.free.card ≤ n := by simpa using Finset.card_le_univ s.pool.free
  exact (normalizeWidths_steps_le s p d g hB).trans
    (Nat.add_le_add hf (SparseRepairGraph.rawRows_card_le _))

end SortingAdversary.Optimal.WidthRepair
