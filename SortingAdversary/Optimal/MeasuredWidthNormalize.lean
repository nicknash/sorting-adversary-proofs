import SortingAdversary.Optimal.MeasuredEarlyNormalize
import SortingAdversary.Optimal.MeasuredScaleDecision
import SortingAdversary.Optimal.MeasuredScaleGroup
import SortingAdversary.Optimal.TraceAppendWork
import SortingAdversary.Optimal.MeasuredRepairBounds

/-!
# Counted complete width normalization

The executable recursion performs all actual W1/W2 scans, W3 reservations,
chronological pins, stored-table updates and trace copies. The reference
normalizer appears only in the proof that the entire returned result,
including its event annotations, is identical. No repair callback remains.
-/

namespace SortingAdversary.Optimal.MeasuredWidthNormalize

open PrimitiveWork WidthRepair RepresentationWork LocalOracle

variable {n : ℕ} {s : State n}

def finish (p : ScaleParameters) (early : EarlyResult s p.width)
    (selected : selectScale early.final p = none) : WidthResult s p where
  final := early.final
  trace := early.trace
  events := .early early.trace early.events
  incident := early.incident
  bound := early.bound
  normal := { toEarlyNormal := early.normal, component := (selectScale_none early.final p).mp selected }

theorem finish_actual (p : ScaleParameters) (d : ℕ) (g : SparseBounds s.rows p.H d)
    (hB : ComparableBound s p.width.B) (early : EarlyResult s p.width)
    (actual : early = WidthRepair.normalizeEarly s p.width hB)
    (selected : selectScale early.final p = none) :
    finish p early selected = WidthRepair.normalizeWidths s p d g hB := by
  subst early
  conv_rhs => unfold WidthRepair.normalizeWidths
  dsimp only
  split
  · rfl
  · rename_i trigger htrigger
    have hbad : none = some trigger := selected.symm.trans htrigger
    cases hbad

def combine (p : ScaleParameters) (early : EarlyResult s p.width) (trigger : ScaleTrigger early.final p)
    (selected : selectScale early.final p = some trigger)
    (group : ScaleRunResult early.final early.final p trigger early.normal (List.finRange p.J))
    (rest : WidthResult group.final p) (trace : Trace s rest.final)
    (actual : trace = early.trace.append (group.trace.append rest.trace)) : WidthResult s p where
  final := rest.final
  trace := trace
  events := by
    rw [actual]
    exact .scale early.trace early.events trigger selected early.normal group.trace group.events rest.trace rest.events
  incident := by
    rw [actual]
    exact early.trace.incidentFrom_append (group.trace.append rest.trace) early.incident
      (group.trace.incidentFrom_append rest.trace
        (group.trace.incidentFrom_mono early.trace.active_old group.incident)
        (rest.trace.incidentFrom_mono (early.trace.append group.trace).active_old rest.incident))
  bound := rest.bound
  normal := rest.normal

theorem combine_actual (p : ScaleParameters) (d : ℕ) (g : SparseBounds s.rows p.H d)
    (hB : ComparableBound s p.width.B) (early : EarlyResult s p.width)
    (early_actual : early = WidthRepair.normalizeEarly s p.width hB)
    (trigger : ScaleTrigger early.final p) (selected : selectScale early.final p = some trigger)
    (group : ScaleRunResult early.final early.final p trigger early.normal (List.finRange p.J))
    (group_actual : group = executeScale early.final p trigger early.normal d (early.trace.sparseBounds g) early.bound)
    (rest : WidthResult group.final p)
    (rest_actual : rest = WidthRepair.normalizeWidths group.final p d
      (group.trace.sparseBounds (early.trace.sparseBounds g)) group.bound)
    (trace : Trace s rest.final) (trace_actual : trace = early.trace.append (group.trace.append rest.trace)) :
    combine p early trigger selected group rest trace trace_actual = WidthRepair.normalizeWidths s p d g hB := by
  subst early
  subst group
  subst rest
  subst trace
  conv_rhs => unfold WidthRepair.normalizeWidths
  dsimp only
  split
  · rename_i hnone
    have hbad : some trigger = none := selected.symm.trans hnone
    cases hbad
  · rename_i chosen hchosen
    have heq : chosen = trigger := Option.some.inj (hchosen.symm.trans selected)
    subst chosen
    rfl

theorem group_measure_lt (p : ScaleParameters) (early : EarlyResult s p.width)
    (trigger : ScaleTrigger early.final p)
    (group : ScaleRunResult early.final early.final p trigger early.normal (List.finRange p.J)) :
    group.final.measure < s.measure := by
  have he := early.trace.length_add_measure_le
  have hg := group.trace.length_add_measure_le
  have hl := group.length
  simp only [List.length_finRange] at hl
  have hp := p.J_pos
  omega

def normalizeWidths {s : State n} (a : LocalAccess s) (ha : AccessBound a 2)
    (p : ScaleParameters) (d : ℕ) (g : SparseBounds s.rows p.H d)
    (hB : ComparableBound s p.width.B) : Result (Output s p d g hB) :=
  let early := MeasuredEarlyNormalize.normalizeEarly a ha p.width hB
  let selection := MeasuredScaleDecision.select early.value.access p
  match hs : selection.value with
  | none =>
    have selected : selectScale early.value.result.final p = none :=
      (MeasuredScaleDecision.select_value early.value.access p).symm.trans hs
    let result := finish p early.value.result selected
    ⟨⟨result, early.value.access,
      finish_actual p d g hB early.value.result early.value.actual selected, early.value.cached⟩,
      early.work + selection.work + 8⟩
  | some trigger =>
    have selected : selectScale early.value.result.final p = some trigger :=
      (MeasuredScaleDecision.select_value early.value.access p).symm.trans hs
    let group := MeasuredScaleGroup.execute early.value.access early.value.cached p trigger early.value.result.normal d
      (early.value.result.trace.sparseBounds g) early.value.result.bound
    let rest := normalizeWidths group.value.access group.value.cached p d
      (group.value.result.trace.sparseBounds (early.value.result.trace.sparseBounds g)) group.value.result.bound
    let joinedGroup := TraceAppendWork.append group.value.result.trace rest.value.result.trace
    let joined := TraceAppendWork.append early.value.result.trace joinedGroup.value
    have joined_actual : joined.value = early.value.result.trace.append
        (group.value.result.trace.append rest.value.result.trace) := by
      simp only [joined, joinedGroup, TraceAppendWork.append_value]
    let result := combine p early.value.result trigger selected group.value.result rest.value.result joined.value joined_actual
    ⟨⟨result, rest.value.access,
      combine_actual p d g hB early.value.result early.value.actual trigger selected group.value.result group.value.actual
        rest.value.result rest.value.actual joined.value joined_actual, rest.value.cached⟩,
      early.work + selection.work + group.work + rest.work + joinedGroup.work + joined.work + 16⟩
termination_by s.measure
decreasing_by
  exact group_measure_lt p early.value.result trigger group.value.result

@[simp] theorem normalizeWidths_actual (a : LocalAccess s) (ha : AccessBound a 2)
    (p : ScaleParameters) (d : ℕ) (g : SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) :
    (normalizeWidths a ha p d g hB).value.result = WidthRepair.normalizeWidths s p d g hB :=
  (normalizeWidths a ha p d g hB).value.actual

def kernelBound (n cap : ℕ) (p : ScaleParameters) : ℕ :=
  (n + n * n + 1) * MeasuredEarlyNormalize.kernelBound n cap p.width +
    MeasuredScaleDecision.workBound n 2 p + MeasuredScaleGroup.workBound n cap p +
    4 * (n + n * n) + 32

theorem normalizeWidths_work_budget {s : State n} (a : LocalAccess s) (ha : AccessBound a 2)
    (p : ScaleParameters) (d : ℕ) (g : SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B)
    (cap : ℕ) (hcap : MeasuredRepairBounds.size s ≤ cap) :
    (normalizeWidths a ha p d g hB).work ≤ (s.measure + 1) * kernelBound n cap p := by
  let early := MeasuredEarlyNormalize.normalizeEarly a ha p.width hB
  have he := MeasuredEarlyNormalize.normalizeEarly_work_budget a ha p.width hB cap hcap
  have hmeasure := MeasuredRepairBounds.measure_le s
  have hemul := Nat.mul_le_mul_right (MeasuredEarlyNormalize.kernelBound n cap p.width)
    (Nat.add_le_add_right hmeasure 1)
  have hearly : early.work ≤ (n + n * n + 1) * MeasuredEarlyNormalize.kernelBound n cap p.width :=
    he.trans hemul
  have hs := MeasuredScaleDecision.select_work_le early.value.access early.value.cached p
  have hsize := (MeasuredRepairBounds.trace_size_le early.value.result.trace).trans hcap
  unfold normalizeWidths
  dsimp only
  split
  · have hkernel : (n + n * n + 1) * MeasuredEarlyNormalize.kernelBound n cap p.width +
        MeasuredScaleDecision.workBound n 2 p + 8 ≤ kernelBound n cap p := by
      unfold kernelBound
      omega
    have hmul := Nat.le_mul_of_pos_left (kernelBound n cap p) (by omega : 0 < s.measure + 1)
    dsimp only [early] at hearly hs
    dsimp only
    omega
  · rename_i trigger selected
    let group := MeasuredScaleGroup.execute early.value.access early.value.cached p trigger early.value.result.normal d
      (early.value.result.trace.sparseBounds g) early.value.result.bound
    have hgroupSize := (MeasuredRepairBounds.trace_size_le group.value.result.trace).trans hsize
    have ih := normalizeWidths_work_budget group.value.access group.value.cached p d
      (group.value.result.trace.sparseBounds (early.value.result.trace.sparseBounds g)) group.value.result.bound cap hgroupSize
    have hg := MeasuredScaleGroup.execute_work_le early.value.access early.value.cached p trigger
      early.value.result.normal d (early.value.result.trace.sparseBounds g) early.value.result.bound
    have hgmono := MeasuredScaleGroup.workBound_mono (n := n) p
      ((Nat.le_add_right early.value.result.final.pool.palette early.value.result.final.measure).trans hsize)
    have hlt := group_measure_lt p early.value.result trigger group.value.result
    have hmul := Nat.mul_le_mul_right (kernelBound n cap p) (Nat.succ_le_of_lt hlt)
    have hlenEarly := MeasuredRepairBounds.trace_length_le early.value.result.trace
    have hlenGroup := MeasuredRepairBounds.trace_length_le group.value.result.trace
    simp only [TraceAppendWork.append_work]
    simp only [kernelBound, Nat.succ_eq_add_one] at hmul ih ⊢
    dsimp only [group, early] at hearly hs ih hg hgmono hmul hlenEarly hlenGroup
    rw [Nat.add_mul, one_mul]
    omega
termination_by s.measure
decreasing_by exact group_measure_lt p early.value.result _ group.value.result

def executor : Executor n := fun a ha p d g hB => normalizeWidths a ha p d g hB

theorem executor_bound (p : ScaleParameters) (d cap : ℕ) :
    MeasuredRepairBounds.WidthBound (executor (n := n)) p d cap
      ((n + n * n + 1) * kernelBound n cap p) := by
  intro s a ha g hB hcap
  have h := normalizeWidths_work_budget a ha p d g hB cap hcap
  exact h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (MeasuredRepairBounds.measure_le s) 1))

end SortingAdversary.Optimal.MeasuredWidthNormalize
