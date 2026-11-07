import SortingAdversary.Optimal.MeasuredScalePlan
import SortingAdversary.Optimal.MeasuredPinAs
import SortingAdversary.Optimal.WidthScale

/-!
# Counted chronological execution of an actual scale reservation

A reservation's labels, central intervals, hub blocks and colours are
materialized once. The loop reads those records in order, computes each
actual insertion receipt and calls the measured pin executor. Only erased
certificates refer to the semantic `ScaleContext.update` or `runScaleAux`.
-/

namespace SortingAdversary.Optimal.MeasuredScaleGroup

open PrimitiveWork WidthRepair RepresentationWork LocalOracle

variable {n : ℕ} {s start current : State n} {p : ScaleParameters}
variable {trigger : ScaleTrigger start p} {normal : EarlyNormal start p.width.W₀ p.width.L}
variable {pending : List (Fin p.J)}

def move (a : LocalAccess current) (plan : MeasuredScalePlan.Plan trigger normal)
    (context : ScaleContext start current p trigger pending) (i : Fin p.J) (hi : i ∈ pending) :
    Result (MeasuredPin.Output (context.update normal i hi)) :=
  let row := plan.entries[i]
  let colour : Fin (current.pool.palette + 1) :=
    ⟨row.colour.val, by rw [context.paletteEq]; exact row.colour.isLt⟩
  let charge := WidthScalarWork.scale p.width.B (row.upper - row.lower)
  have hv : row.vertex = (context.update normal i hi).vertex := by
    change row.vertex = trigger.vertices i
    exact congrArg ScaleBlocksWork.TypedEntry.vertex (plan.exact i)
  have hc : colour = (context.update normal i hi).colour := by
    apply Fin.ext
    exact congrArg (fun entry => entry.colour.val) (plan.exact i)
  have hq : charge.value = (context.update normal i hi).charge := by
    simp only [charge, WidthScalarWork.scale_value]
    have hl := congrArg ScaleBlocksWork.TypedEntry.lower (plan.exact i)
    have hu := congrArg ScaleBlocksWork.TypedEntry.upper (plan.exact i)
    change ((2 * 4 ^ p.width.B * (row.upper - row.lower) : ℕ) : ℚ) =
      ((2 * 4 ^ p.width.B * (trigger.upper i.val - trigger.lower i.val) : ℕ) : ℚ)
    rw [show row.lower = ScaleMass.intervalLower start.numerical (trigger.vertices i) from hl,
      show row.upper = ScaleMass.intervalUpper start.numerical (trigger.vertices i) from hu,
      ScaleTrigger.lower_fin, ScaleTrigger.upper_fin]
  let pinned := MeasuredPinAs.pin a (context.update normal i hi) row.vertex hv colour hc charge.value hq
  ⟨pinned.value, charge.work + pinned.work + 16⟩

def moveBound (n palette B : ℕ) : ℕ := 2 * B + 5 + MeasuredPin.workBound n palette 2 + 16

theorem move_work_le (a : LocalAccess current) (ha : AccessBound a 2)
    (plan : MeasuredScalePlan.Plan trigger normal)
    (context : ScaleContext start current p trigger pending) (i : Fin p.J) (hi : i ∈ pending) :
    (move a plan context i hi).work ≤ moveBound n current.pool.palette p.width.B := by
  unfold move
  dsimp only
  rw [WidthScalarWork.scale_work]
  unfold moveBound
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact MeasuredPinAs.pin_work_le a ha _ _ _ _ _ _ _

structure Output (start current : State n) (p : ScaleParameters) (trigger : ScaleTrigger start p)
    (normal : EarlyNormal start p.width.W₀ p.width.L) (d : ℕ)
    (g : SparseBounds start.rows p.H d) (pending : List (Fin p.J))
    (hnd : pending.Nodup) (context : ScaleContext start current p trigger pending) where
  result : ScaleRunResult start current p trigger normal pending
  access : LocalAccess result.final
  actual : result = runScaleAux start current p trigger normal d g pending hnd context
  cached : AccessBound access 2

def prepend (context : ScaleContext start current p trigger (i :: rest))
    (update : PinUpdate current) (actual : update = context.update normal i (List.mem_cons_self ..))
    (tail : ScaleRunResult start update.next p trigger normal rest) :
    ScaleRunResult start current p trigger normal (i :: rest) where
  final := tail.final
  trace := .cons (.pin update) tail.trace
  events := .cons i update
    (by subst update; rfl) (by subst update; rfl)
    (by subst update; exact context.interior normal i (List.mem_cons_self ..))
    (by subst update; rfl) (by subst update; rfl) tail.trace tail.events
  incident := by
    refine ⟨?_, tail.incident⟩
    subst update
    exact trigger.vertices_incident normal i
  length := by change tail.trace.length + 1 = rest.length + 1; rw [tail.length]
  bound := tail.bound
  palette := tail.palette.trans (by subst update; rfl)
  order := tail.order.trans (by subst update; rfl)

theorem prepend_actual (context : ScaleContext start current p trigger (i :: rest))
    (d : ℕ) (g : SparseBounds start.rows p.H d) (hnd : (i :: rest).Nodup)
    (update : PinUpdate current) (actual : update = context.update normal i (List.mem_cons_self ..))
    (nextContext : ScaleContext start update.next p trigger rest)
    (tail : ScaleRunResult start update.next p trigger normal rest)
    (tail_actual : tail = runScaleAux start update.next p trigger normal d g rest hnd.of_cons nextContext) :
    prepend context update actual tail = runScaleAux start current p trigger normal d g (i :: rest) hnd context := by
  subst update
  subst tail
  conv_rhs => unfold runScaleAux
  rfl

def run {current : State n} (a : LocalAccess current) (ha : AccessBound a 2)
    (plan : MeasuredScalePlan.Plan trigger normal) (d : ℕ) (g : SparseBounds start.rows p.H d)
    (pending : List (Fin p.J)) (hnd : pending.Nodup) (context : ScaleContext start current p trigger pending) :
    Result (Output start current p trigger normal d g pending hnd context) :=
  match pending with
  | [] =>
    ⟨⟨⟨current, .nil current, .nil current, trivial, rfl, context.bound, rfl, HEq.rfl⟩,
      a, rfl, ha⟩, 1⟩
  | i :: rest =>
    let pinned := move a plan context i (List.mem_cons_self ..)
    have nextContext : ScaleContext start pinned.value.update.next p trigger rest := by
      rw [pinned.value.exact]
      exact context.advance normal g hnd
    let tail := run pinned.value.access pinned.value.bounded plan d g rest hnd.of_cons nextContext
    let result := prepend context pinned.value.update pinned.value.exact tail.value.result
    ⟨⟨result, tail.value.access,
      prepend_actual context d g hnd pinned.value.update pinned.value.exact nextContext tail.value.result tail.value.actual,
      tail.value.cached⟩, pinned.work + tail.work + 8⟩

/-- The current and initial palettes agree throughout a scale group. -/
theorem run_work_le {current : State n} (a : LocalAccess current) (ha : AccessBound a 2)
    (plan : MeasuredScalePlan.Plan trigger normal) (d : ℕ) (g : SparseBounds start.rows p.H d)
    (pending : List (Fin p.J)) (hnd : pending.Nodup) (context : ScaleContext start current p trigger pending) :
    (run a ha plan d g pending hnd context).work ≤
      pending.length * (moveBound n start.pool.palette p.width.B + 8) + 1 := by
  induction pending generalizing current with
  | nil => simp only [run, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons i rest ih =>
    let pinned := move a plan context i (List.mem_cons_self ..)
    have nextContext : ScaleContext start pinned.value.update.next p trigger rest := by
      rw [pinned.value.exact]
      exact context.advance normal g hnd
    have ht := ih pinned.value.access pinned.value.bounded hnd.of_cons nextContext
    have hm := move_work_le a ha plan context i (List.mem_cons_self ..)
    rw [context.paletteEq] at hm
    change pinned.work + (run pinned.value.access pinned.value.bounded plan d g rest hnd.of_cons nextContext).work + 8 ≤ _
    change pinned.work ≤ _ at hm
    simp only [List.length_cons, Nat.add_mul, one_mul]
    omega

def initialContext (s : State n) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (hB : ComparableBound s p.width.B) :
    ScaleContext s s p trigger (List.finRange p.J) where
  activeOld := fun _ _ h => h
  publicEq := rfl
  membersEq := rfl
  paletteEq := rfl
  orderEq := HEq.rfl
  bound := hB
  free := fun i _ => s.nonisolated_free (trigger.vertices_incident normal i)
  lower := fun _ _ => rfl
  upper := fun _ _ => rfl

structure GroupOutput (s : State n) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (d : ℕ) (g : SparseBounds s.rows p.H d)
    (hB : ComparableBound s p.width.B) where
  result : ScaleRunResult s s p trigger normal (List.finRange p.J)
  access : LocalAccess result.final
  actual : result = executeScale s p trigger normal d g hB
  cached : AccessBound access 2

def execute (a : LocalAccess s) (ha : AccessBound a 2) (p : ScaleParameters) (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (d : ℕ) (g : SparseBounds s.rows p.H d)
    (hB : ComparableBound s p.width.B) : Result (GroupOutput s p trigger normal d g hB) :=
  let plan := MeasuredScalePlan.build a p trigger normal
  let indices := FiniteLoopWork.indices p.J
  let result := run a ha plan.value d g indices.value (List.nodup_finRange _) (initialContext s p trigger normal hB)
  ⟨⟨result.value.result, result.value.access, result.value.actual, result.value.cached⟩,
    plan.work + indices.work + result.work + 4⟩

def workBound (n palette : ℕ) (p : ScaleParameters) : ℕ :=
  MeasuredScalePlan.workBound n palette 2 p + (3 * p.J + 1) +
    p.J * (moveBound n palette p.width.B + 8) + 5

theorem execute_work_le (a : LocalAccess s) (ha : AccessBound a 2) (p : ScaleParameters)
    (trigger : ScaleTrigger s p) (normal : EarlyNormal s p.width.W₀ p.width.L)
    (d : ℕ) (g : SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (execute a ha p trigger normal d g hB).work ≤ workBound n s.pool.palette p := by
  have hp := MeasuredScalePlan.build_work_le a ha p trigger normal
  have hr := run_work_le a ha (MeasuredScalePlan.build a p trigger normal).value d g
    (List.finRange p.J) (List.nodup_finRange _) (initialContext s p trigger normal hB)
  simp only [List.length_finRange] at hr
  change _ + (3 * p.J + 1) + _ + 4 ≤ _
  dsimp only [FiniteLoopWork.indices]
  unfold workBound
  omega

theorem moveBound_mono {n K L B : ℕ} (hK : K ≤ L) : moveBound n K B ≤ moveBound n L B := by
  unfold moveBound MeasuredPin.workBound
  have h := LocalAccess.cacheBound_mono (n := n) (A := 20) (Nat.succ_le_succ hK) le_rfl
  simp only [Nat.succ_eq_add_one, Nat.reduceMul, Nat.reduceAdd] at h ⊢
  omega

theorem workBound_mono {n K L : ℕ} (p : ScaleParameters) (hK : K ≤ L) :
    workBound n K p ≤ workBound n L p := by
  have hp := MeasuredScalePlan.workBound_mono (n := n) (A := 2) p hK
  have hm := Nat.mul_le_mul_left p.J (Nat.add_le_add_right (moveBound_mono (n := n) (B := p.width.B) hK) 8)
  unfold workBound
  omega

end SortingAdversary.Optimal.MeasuredScaleGroup
