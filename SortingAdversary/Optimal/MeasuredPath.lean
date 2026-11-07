import SortingAdversary.Optimal.MeasuredRepairBounds
import SortingAdversary.Optimal.MeasuredOrdinaryTypes
import SortingAdversary.Optimal.StructuralNormalize
import SortingAdversary.Optimal.FiniteLoopWork

/-!
# Measured execution of reserved paths

The loop below calls its measured width and ordinary executors, tests the
pin returned by the cached getter, and recurses on the resulting state.
The reference executor occurs only in erased correctness certificates.
Concrete numerical executors instantiate the two interfaces downstream.
-/

namespace SortingAdversary.Optimal.MeasuredPath

open WidthRepair StructuralNormalize RepresentationWork LocalOracle PoolState

set_option maxRecDepth 8192

variable {n : ℕ}

def one {s : State n} (ordinary : OrdinaryPromotion.Move s) :
    Trace s ordinary.update.next := .cons (.pin ordinary.update) (.nil _)

def moved (p : Parameters) (start current : State n) (reservation : Reservation start p.H)
    (v : Fin n) (pending : List (Fin n))
    (subset : ∀ x ∈ v :: pending, x ∈ reservation.labels) (context : Context start current)
    (width : WidthResult current p.scale) (ordinary : OrdinaryPromotion.Move width.final)
    (vertex : ordinary.update.vertex = v)
    (rest : PathResult p start ordinary.update.next reservation pending) :
    PathResult p start current reservation (v :: pending) where
  final := rest.final
  trace := width.trace.append (.cons (.pin ordinary.update) rest.trace)
  events := .move v (subset v (List.mem_cons_self ..)) width.trace width.events ordinary vertex
    rest.trace rest.events
  incident := width.trace.incidentFrom_append _
    (width.trace.incidentFrom_mono context.active width.incident)
    ⟨by
      change (GraphBalls.neighbors start.rows.active ordinary.update.vertex).Nonempty
      rw [vertex]
      exact reservation.incident p.path_two (subset v (List.mem_cons_self ..)), rest.incident⟩
  bound := rest.bound
  done := by
    intro x hx
    rcases List.mem_cons.mp hx with heq | hx
    · intro hf
      have hh := rest.trace.free_subset hf
      rw [heq] at hh
      change v ∈ (width.final.pool.installPromotion ordinary.update.vertex ordinary.update.free
        ordinary.update.colour ordinary.update.result).free at hh
      rw [Pool.installPromotion_free] at hh
      exact (Finset.mem_erase.mp hh).1 vertex.symm
    · exact rest.done x hx

def skipped (p : Parameters) (start current : State n) (reservation : Reservation start p.H)
    (v : Fin n) (pending : List (Fin n))
    (subset : ∀ x ∈ v :: pending, x ∈ reservation.labels) (context : Context start current)
    (width : WidthResult current p.scale) (hfree : width.final.pool.pins v ≠ none)
    (rest : PathResult p start width.final reservation pending) :
    PathResult p start current reservation (v :: pending) where
  final := rest.final
  trace := width.trace.append rest.trace
  events := .skip v (subset v (List.mem_cons_self ..)) width.trace width.events
    (fun h => hfree ((width.final.pool.free_iff v).mp h)) rest.trace rest.events
  incident := width.trace.incidentFrom_append rest.trace
    (width.trace.incidentFrom_mono context.active width.incident) rest.incident
  bound := rest.bound
  done := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact fun hf => hfree ((width.final.pool.free_iff _).mp (rest.trace.free_subset hf))
    · exact rest.done x hx

theorem moved_actual (p : Parameters) (start current : State n)
    (reservation : Reservation start p.H) (v : Fin n) (pending : List (Fin n))
    (subset : ∀ x ∈ v :: pending, x ∈ reservation.labels) (context : Context start current)
    (g : SparseBounds current.rows p.scale.H p.d) (hB : ComparableBound current p.scale.width.B)
    (width : WidthResult current p.scale) (hw : width = normalizeWidths current p.scale p.d g hB)
    (hfree : width.final.pool.pins v = none)
    (ordinary : OrdinaryPromotion.Move width.final)
    (ho : ordinary = OrdinaryPromotion.make width.final p.scale.H p.d (width.trace.sparseBounds g)
      p.scale.R (by positivity) v (width.normal.markCondition p.d (1 / 16) p.minimum v) hfree
      ((context.advance width.trace).mate (reservation.mate p.path_two (subset v (List.mem_cons_self ..)))))
    (vertex : ordinary.update.vertex = v)
    (rest : PathResult p start ordinary.update.next reservation pending)
    (hr : rest = StructuralNormalize.runPath p start ordinary.update.next reservation pending
      (fun x hx => subset x (List.mem_cons_of_mem v hx))
      ((context.advance width.trace).advance (one ordinary))
      ((one ordinary).sparseBounds (width.trace.sparseBounds g))
      (comparableBound_trace (one ordinary) width.bound)) :
    moved p start current reservation v pending subset context width ordinary vertex rest =
      StructuralNormalize.runPath p start current reservation (v :: pending) subset context g hB := by
  subst width
  subst ordinary
  subst rest
  simp only [StructuralNormalize.runPath, dif_pos hfree]
  rfl

theorem skipped_actual (p : Parameters) (start current : State n)
    (reservation : Reservation start p.H) (v : Fin n) (pending : List (Fin n))
    (subset : ∀ x ∈ v :: pending, x ∈ reservation.labels) (context : Context start current)
    (g : SparseBounds current.rows p.scale.H p.d) (hB : ComparableBound current p.scale.width.B)
    (width : WidthResult current p.scale) (hw : width = normalizeWidths current p.scale p.d g hB)
    (hfree : width.final.pool.pins v ≠ none)
    (rest : PathResult p start width.final reservation pending)
    (hr : rest = StructuralNormalize.runPath p start width.final reservation pending
      (fun x hx => subset x (List.mem_cons_of_mem v hx)) (context.advance width.trace)
      (width.trace.sparseBounds g) width.bound) :
    skipped p start current reservation v pending subset context width hfree rest =
      StructuralNormalize.runPath p start current reservation (v :: pending) subset context g hB := by
  subst width
  subst rest
  simp only [StructuralNormalize.runPath, dif_neg hfree]
  rfl

structure Output (p : Parameters) (start current : State n) (reservation : Reservation start p.H)
    (pending : List (Fin n)) (subset : ∀ v ∈ pending, v ∈ reservation.labels)
    (context : Context start current)
    (g : SparseBounds current.rows p.scale.H p.d) (hB : ComparableBound current p.scale.width.B) where
  result : PathResult p start current reservation pending
  access : LocalAccess result.final
  actual : result = StructuralNormalize.runPath p start current reservation pending subset context g hB
  cached : AccessBound access 2

def run (widthExecutor : MeasuredWidthNormalize.Executor n) (p : Parameters)
    (ordinaryExecutor : MeasuredOrdinaryPromotion.Executor n p.scale.H p.d p.scale.R)
    (start current : State n) (reservation : Reservation start p.H)
    (pending : List (Fin n)) (subset : ∀ v ∈ pending, v ∈ reservation.labels)
    (context : Context start current)
    (g : SparseBounds current.rows p.scale.H p.d) (hB : ComparableBound current p.scale.width.B)
    (access : LocalAccess current) (cached : AccessBound access 2) :
    PrimitiveWork.Result (Output p start current reservation pending subset context g hB) :=
  match pending with
  | [] => ⟨⟨⟨current, .nil current, .nil current, trivial, hB, by simp⟩,
      access, rfl, cached⟩, 1⟩
  | v :: pending =>
    let measuredWidth := widthExecutor access cached p.scale p.d g hB
    let width := measuredWidth.value.result
    let pin := measuredWidth.value.access.pin v
    let nextContext := context.advance width.trace
    if hp : pin.value = none then
      have hfree : width.final.pool.pins v = none :=
        (measuredWidth.value.access.pin_value v).symm.trans hp
      let measuredOrdinary := ordinaryExecutor measuredWidth.value.access measuredWidth.value.cached
        (width.trace.sparseBounds g) (by positivity) v
        (width.normal.markCondition p.d (1 / 16) p.minimum v) hfree
        (nextContext.mate (reservation.mate p.path_two (subset v (List.mem_cons_self ..))))
      let ordinary := measuredOrdinary.value.result
      have vertex : ordinary.update.vertex = v := by
        dsimp only [ordinary]
        rw [measuredOrdinary.value.actual]
        rfl
      let rest := run widthExecutor p ordinaryExecutor start ordinary.update.next reservation pending
        (fun x hx => subset x (List.mem_cons_of_mem v hx)) (nextContext.advance (one ordinary))
        ((one ordinary).sparseBounds (width.trace.sparseBounds g))
        (comparableBound_trace (one ordinary) width.bound)
        measuredOrdinary.value.access measuredOrdinary.value.cached
      let result := moved p start current reservation v pending subset context width ordinary vertex
        rest.value.result
      ⟨⟨result, rest.value.access,
        moved_actual p start current reservation v pending subset context g hB width
          measuredWidth.value.actual hfree ordinary measuredOrdinary.value.actual vertex
          rest.value.result rest.value.actual, rest.value.cached⟩,
        measuredWidth.work + pin.work + measuredOrdinary.work + rest.work + 2 * width.trace.length + 12⟩
    else
      have hfree : width.final.pool.pins v ≠ none := by
        intro h
        exact hp ((measuredWidth.value.access.pin_value v).trans h)
      let rest := run widthExecutor p ordinaryExecutor start width.final reservation pending
        (fun x hx => subset x (List.mem_cons_of_mem v hx)) nextContext
        (width.trace.sparseBounds g) width.bound measuredWidth.value.access measuredWidth.value.cached
      let result := skipped p start current reservation v pending subset context width hfree rest.value.result
      ⟨⟨result, rest.value.access,
        skipped_actual p start current reservation v pending subset context g hB width
          measuredWidth.value.actual hfree rest.value.result rest.value.actual, rest.value.cached⟩,
        measuredWidth.work + pin.work + rest.work + 2 * width.trace.length + 10⟩

def workBound (n length widthWork ordinaryWork : ℕ) : ℕ :=
  length * (widthWork + ordinaryWork + 2 * (n + n * n) + 14) + 1

theorem run_work_le (widthExecutor : MeasuredWidthNormalize.Executor n) (p : Parameters)
    (ordinaryExecutor : MeasuredOrdinaryPromotion.Executor n p.scale.H p.d p.scale.R)
    (cap widthWork ordinaryWork : ℕ)
    (hwidth : MeasuredRepairBounds.WidthBound widthExecutor p.scale p.d cap widthWork)
    (hordinary : MeasuredRepairBounds.OrdinaryBound p ordinaryExecutor cap ordinaryWork)
    (start current : State n) (reservation : Reservation start p.H)
    (pending : List (Fin n)) (subset : ∀ v ∈ pending, v ∈ reservation.labels)
    (context : Context start current)
    (g : SparseBounds current.rows p.scale.H p.d) (hB : ComparableBound current p.scale.width.B)
    (access : LocalAccess current) (cached : AccessBound access 2)
    (hsize : MeasuredRepairBounds.size current ≤ cap) :
    (run widthExecutor p ordinaryExecutor start current reservation pending subset context g hB
      access cached).work ≤ workBound n pending.length widthWork ordinaryWork := by
  induction pending generalizing current with
  | nil => simp only [run, List.length_nil, workBound, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons v pending ih =>
    let measuredWidth := widthExecutor access cached p.scale p.d g hB
    let width := measuredWidth.value.result
    have hw : measuredWidth.work ≤ widthWork := hwidth access cached g hB hsize
    have hs : MeasuredRepairBounds.size width.final ≤ cap :=
      (MeasuredRepairBounds.trace_size_le width.trace).trans hsize
    have hl : width.trace.length ≤ n + n * n := MeasuredRepairBounds.trace_length_le width.trace
    have hp : (measuredWidth.value.access.pin v).work ≤ 2 := measuredWidth.value.cached.pin v
    rw [run]
    dsimp only
    split
    · rename_i hpnone
      have hfree : width.final.pool.pins v = none :=
        (measuredWidth.value.access.pin_value v).symm.trans hpnone
      let measuredOrdinary := ordinaryExecutor measuredWidth.value.access measuredWidth.value.cached
        (width.trace.sparseBounds g) (by positivity) v
        (width.normal.markCondition p.d (1 / 16) p.minimum v) hfree
        ((context.advance width.trace).mate (reservation.mate p.path_two (subset v (List.mem_cons_self ..))))
      let ordinary := measuredOrdinary.value.result
      have ho : measuredOrdinary.work ≤ ordinaryWork :=
        hordinary measuredWidth.value.access measuredWidth.value.cached (width.trace.sparseBounds g) v
          (width.normal.markCondition p.d (1 / 16) p.minimum v) hfree
          ((context.advance width.trace).mate (reservation.mate p.path_two (subset v (List.mem_cons_self ..)))) hs
      have ht := ih (current := ordinary.update.next)
        (fun x hx => subset x (List.mem_cons_of_mem v hx))
        ((context.advance width.trace).advance (one ordinary))
        ((one ordinary).sparseBounds (width.trace.sparseBounds g))
        (comparableBound_trace (one ordinary) width.bound)
        measuredOrdinary.value.access measuredOrdinary.value.cached
        ((MeasuredRepairBounds.pin_size_le ordinary.update).trans hs)
      change measuredWidth.work + (measuredWidth.value.access.pin v).work + measuredOrdinary.work +
        (run widthExecutor p ordinaryExecutor start ordinary.update.next reservation pending _ _ _ _
          measuredOrdinary.value.access measuredOrdinary.value.cached).work + 2 * width.trace.length + 12 ≤ _
      simp only [workBound, List.length_cons, Nat.add_mul, Nat.one_mul] at ht ⊢
      dsimp only [measuredWidth, width, measuredOrdinary, ordinary] at hw hs hl hp ho ht ⊢
      omega
    · rename_i hpnone
      have ht := ih (current := width.final)
        (fun x hx => subset x (List.mem_cons_of_mem v hx)) (context.advance width.trace)
        (width.trace.sparseBounds g) width.bound measuredWidth.value.access measuredWidth.value.cached hs
      change measuredWidth.work + (measuredWidth.value.access.pin v).work +
        (run widthExecutor p ordinaryExecutor start width.final reservation pending _ _ _ _
          measuredWidth.value.access measuredWidth.value.cached).work + 2 * width.trace.length + 10 ≤ _
      simp only [workBound, List.length_cons, Nat.add_mul, Nat.one_mul] at ht ⊢
      dsimp only [measuredWidth, width] at hw hs hl hp ht ⊢
      omega

end SortingAdversary.Optimal.MeasuredPath
