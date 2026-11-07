import SortingAdversary.Optimal.LedgerTreeTransitions
import SortingAdversary.Optimal.WidthRepair

/-!
# Actual sparse rows supply chronological endpoint charges

The invariant below relates each currently active row to an actual recorded
free--free physical call at its immutable node. It is preserved by the
concrete public-row insertion and by every deletion performed during width
repair. Both promotion witnesses and the degree charge are derived from this
row correspondence; neither follows merely from public comparability.
-/

namespace SortingAdversary.Optimal.LedgerSourceHistory

open PoolState PoolTree PoolTree.Tree PoolTreeTraversal TreeChronology
open LedgerTreeBridge LedgerTreeTransitions IncidenceLedger NumericalRepresentation

variable {n K : ℕ}

def RecordedRows (calls : List (Option (Row n))) (identity : ℕ)
    (rows : Fin n → Fin n → Bool) : Prop :=
  ∀ u v, rows u v = true → some (Row.mk identity u v) ∈ calls

theorem RecordedRows.empty (identity : ℕ) :
    RecordedRows ([] : List (Option (Row n))) identity (fun _ _ => false) := by
  intro u v h
  contradiction

theorem RecordedRows.mono {calls : List (Option (Row n))} {identity : ℕ}
    {E F : Fin n → Fin n → Bool} (h : RecordedRows calls identity E)
    (hsub : ∀ u v, F u v = true → E u v = true) : RecordedRows calls identity F :=
  fun u v huv => h u v (hsub u v huv)

theorem RecordedRows.append {calls : List (Option (Row n))} {identity : ℕ}
    {E : Fin n → Fin n → Bool} (h : RecordedRows calls identity E)
    (extra : List (Option (Row n))) : RecordedRows (calls ++ extra) identity E :=
  fun u v huv => List.mem_append_left _ (h u v huv)

theorem recorded_endpoints_of_row (calls : List (Option (Row n))) (identity : ℕ)
    (u v : Fin n) (h : some (Row.mk identity u v) ∈ calls) :
    ∃ i, i < calls.length ∧
      recordedEndpoint calls (i, false) = some (identity, u) ∧
      recordedEndpoint calls (i, true) = some (identity, v) := by
  obtain ⟨i, hi, hrow⟩ := List.mem_iff_getElem.mp h
  refine ⟨i, hi, ?_, ?_⟩ <;>
    simp only [recordedEndpoint, List.getElem?_eq_getElem hi, hrow, Option.join_some,
      Option.map_some, Row.endpoint, Bool.false_eq_true, if_false, if_true]

/-- Even after later pins retire an incident edge, its endpoint is retained
in the immutable physical-call history. -/
theorem RecordedRows.incident {calls : List (Option (Row n))} {identity : ℕ}
    {E : Fin n → Fin n → Bool} (h : RecordedRows calls identity E) (v : Fin n)
    (hv : (GraphBalls.neighbors E v).Nonempty) : (incidences calls (identity, v)).Nonempty := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨_, hforward | hbackward⟩ := (GraphBalls.mem_neighbors E v w).mp hw
  · obtain ⟨i, hi, hleft, _⟩ := recorded_endpoints_of_row calls identity v w (h v w hforward)
    exact ⟨(i, false), (mem_incidences _ _ _).mpr ⟨hi, hleft⟩⟩
  · obtain ⟨i, hi, _, hright⟩ := recorded_endpoints_of_row calls identity w v (h w v hbackward)
    exact ⟨(i, true), (mem_incidences _ _ _).mpr ⟨hi, hright⟩⟩

theorem neighbor_of_recorded_endpoints (s : IncidenceLedger.State n)
    (x y : Location n) (e : Endpoint) (ht : e.1 < s.calls.length)
    (hx : recordedEndpoint s.calls e = some x)
    (hy : recordedEndpoint s.calls (e.1, !e.2) = some y)
    (hyfree : y ∈ s.free) (hne : y ≠ x) : some y ∈ IncidenceLedger.neighbors s x := by
  apply Finset.mem_image.mpr
  refine ⟨e, ?_, hy⟩
  apply Finset.mem_filter.mpr
  refine ⟨(mem_incidences _ _ _).mpr ⟨ht, hx⟩, ?_⟩
  simp only [hy, Option.any_some, decide_eq_true_eq]
  exact ⟨hyfree, hne⟩

theorem RecordedRows.neighbor_mem {s : IncidenceLedger.State n} {identity : ℕ}
    {E : Fin n → Fin n → Bool} (h : RecordedRows s.calls identity E)
    (hfree : ∀ u v, E u v = true → (identity, u) ∈ s.free ∧ (identity, v) ∈ s.free)
    (v w : Fin n) (hw : w ∈ GraphBalls.neighbors E v) :
    some (identity, w) ∈ IncidenceLedger.neighbors s (identity, v) := by
  obtain ⟨hne, hforward | hbackward⟩ := (GraphBalls.mem_neighbors E v w).mp hw
  · obtain ⟨i, hi, hleft, hright⟩ := recorded_endpoints_of_row s.calls identity v w (h v w hforward)
    apply neighbor_of_recorded_endpoints s (identity, v) (identity, w) (i, false) hi hleft
    · exact hright
    · exact (hfree v w hforward).2
    · exact fun heq => hne (congrArg Prod.snd heq)
  · obtain ⟨i, hi, hleft, hright⟩ := recorded_endpoints_of_row s.calls identity w v (h w v hbackward)
    apply neighbor_of_recorded_endpoints s (identity, v) (identity, w) (i, true) hi hright
    · exact hleft
    · exact (hfree w v hbackward).1
    · exact fun heq => hne (congrArg Prod.snd heq)

/-- Distinct neighbors inject into distinct recorded opposite endpoints.
Repeated comparisons do not inflate the graph degree. -/
theorem RecordedRows.degree_le_liveDegree {s : IncidenceLedger.State n} {identity : ℕ}
    {E : Fin n → Fin n → Bool} (h : RecordedRows s.calls identity E)
    (hfree : ∀ u v, E u v = true → (identity, u) ∈ s.free ∧ (identity, v) ∈ s.free)
    (v : Fin n) :
    (GraphBalls.neighbors E v).card ≤ IncidenceLedger.liveDegree s (identity, v) := by
  have hinj : Function.Injective (fun w : Fin n => some (identity, w)) := by
    intro u w heq
    exact congrArg Prod.snd (Option.some.inj heq)
  have hc := Finset.card_image_of_injective (GraphBalls.neighbors E v) hinj
  rw [← hc]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  exact h.neighbor_mem hfree v w hw

/-- The stopping call records a real row exactly when both endpoints were
free in its pre-comparison pool. All calls still occupy a clock position. -/
def callRow (identity : ℕ) (p : Pool n) (a b : Fin n) : Option (Row n) :=
  if p.pins a = none ∧ p.pins b = none then some ⟨identity, a, b⟩ else none

theorem callRow_admissible (s : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n)) (a b : Fin n) (hab : a ≠ b)
    (hrep : Represents s (ctx.plug (.node identity p children))) :
    rowAdmissible s (callRow identity p a b) := by
  unfold callRow
  split
  next hf => exact realRow_admissible s ctx identity p children a b hf.1 hf.2 hab hrep
  next => trivial

theorem RecordedRows.add {calls : List (Option (Row n))} {identity : ℕ}
    (p : Pool n) (rows : SourcePartition p.system p.pins)
    (h : RecordedRows calls identity rows.active) (a b : Fin n) (hab : a ≠ b) :
    RecordedRows (calls ++ [callRow identity p a b]) identity (rows.add a b hab).active := by
  intro u v huv
  have hsplit : rows.active u v = true ∨
      (u = a ∧ v = b ∧ p.pins a = none ∧ p.pins b = none) := by
    simpa only [SourcePartition.add, Bool.or_eq_true, decide_eq_true_eq] using huv
  rcases hsplit with hold | ⟨rfl, rfl, ha, hb⟩
  · exact List.mem_append_left _ (h u v hold)
  · apply List.mem_append_right
    simp [callRow, ha, hb]

theorem RecordedRows.repairStep {calls : List (Option (Row n))} {identity : ℕ}
    {s t : WidthRepair.State n} (h : RecordedRows calls identity s.rows.active)
    (step : WidthRepair.Step s t) : RecordedRows calls identity t.rows.active :=
  h.mono step.active_old

theorem RecordedRows.repairTrace {calls : List (Option (Row n))} {identity : ℕ}
    {s t : WidthRepair.State n} (h : RecordedRows calls identity s.rows.active)
    (trace : WidthRepair.Trace s t) : RecordedRows calls identity t.rows.active := by
  induction trace with
  | nil => exact h
  | cons step rest ih => exact ih (h.repairStep step)

theorem represents_lowerCut (s : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (poolState : WidthRepair.State n) (children : List (ℕ × Tree n))
    (u v : Fin n) (huv : poolState.rows.active u v = true)
    (hratio : 2 * poolState.width v < poolState.width u)
    (hrep : Represents s (ctx.plug (.node identity poolState.pool children))) :
    Represents s (ctx.plug (.node identity (poolState.lowerCut u v huv hratio).pool children)) :=
  represents_poolUpdate s ctx identity poolState.pool (poolState.lowerCut u v huv hratio).pool children
    rfl rfl hrep

theorem represents_upperCut (s : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (poolState : WidthRepair.State n) (children : List (ℕ × Tree n))
    (u v : Fin n) (huv : poolState.rows.active u v = true)
    (hratio : 2 * poolState.width u < poolState.width v)
    (hrep : Represents s (ctx.plug (.node identity poolState.pool children))) :
    Represents s (ctx.plug (.node identity (poolState.upperCut u v huv hratio).pool children)) :=
  represents_poolUpdate s ctx identity poolState.pool (poolState.upperCut u v huv hratio).pool children
    rfl rfl hrep

end SortingAdversary.Optimal.LedgerSourceHistory
