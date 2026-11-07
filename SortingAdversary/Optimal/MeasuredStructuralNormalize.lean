import SortingAdversary.Optimal.MeasuredStructuralTypes

/-!
# The measured degree and reserved-path controller

Each iteration obtains its decisions from counted width, degree, and
longest-path routines. A path reservation reuses the computed longest path.
Actual measured ordinary and reserved-path executions supply the successor
state. Equality to the original complete normalizer is a proof-only field.
-/

namespace SortingAdversary.Optimal.MeasuredStructuralNormalize

open WidthRepair StructuralNormalize RepresentationWork LocalOracle PoolState
open SparseRepairGraph GraphBalls

set_option maxRecDepth 8192

variable {n : ℕ}

def normalize (widthExecutor : MeasuredWidthNormalize.Executor n) (p : Parameters)
    (ordinaryExecutor : MeasuredOrdinaryPromotion.Executor n p.scale.H p.d p.scale.R)
    (s : State n) (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank) :
    PrimitiveWork.Result (Output s p g hB) :=
  let measuredWidth := widthExecutor access cached p.scale p.d g hB
  let width := measuredWidth.value.result
  let graph := width.trace.sparseBounds g
  let degree := RepairSelectWork.degree measuredWidth.value.access p.D
  match hselected : degree.value with
  | some v =>
    have selected : degreeWitness width.final.rows.active width.final.pool.free p.D = some v :=
      (RepairSelectWork.degree_value measuredWidth.value.access p.D).symm.trans hselected
    let hs := degreeWitness_some width.final.rows.active width.final.pool.free p.D selected
    let incident : (neighbors width.final.rows.active v).Nonempty :=
      Finset.card_pos.mp (p.degree_pos.trans_le hs.2)
    let measuredOrdinary := ordinaryExecutor measuredWidth.value.access measuredWidth.value.cached
      graph (by positivity) v (width.normal.markCondition p.d (1 / 16) p.minimum v)
      ((width.final.pool.free_iff v).mp hs.1) (width.final.nonisolated_mate incident)
    let ordinary := measuredOrdinary.value.result
    have vertex : ordinary.update.vertex = v := by
      dsimp only [ordinary]
      rw [measuredOrdinary.value.actual]
      rfl
    let one := MeasuredPath.one ordinary
    let rest := normalize widthExecutor p ordinaryExecutor ordinary.update.next
      (one.sparseBounds graph) (comparableBound_trace one width.bound)
      measuredOrdinary.value.access measuredOrdinary.value.cached rank rank_eq
    let result := degreeResult s p width ordinary (by rw [vertex]; exact selected)
      (by rw [vertex]; exact incident) rest.value.result
    ⟨⟨result, rest.value.access,
      degree_actual s p g hB width measuredWidth.value.actual v selected incident ordinary
        measuredOrdinary.value.actual vertex rest.value.result rest.value.actual,
      rest.value.cached⟩,
      measuredWidth.work + degree.work + measuredOrdinary.work + rest.work + 2 * width.trace.length + 12⟩
  | none =>
    have selected : degreeWitness width.final.rows.active width.final.pool.free p.D = none :=
      (RepairSelectWork.degree_value measuredWidth.value.access p.D).symm.trans hselected
    let path := LongestPathWork.longestChain measuredWidth.value.access.active rank p.scale.H
    have path_eq : path.value = longestChain width.final.rows.active graph.rank p.scale.H := by
      rw [LongestPathWork.longestChain_value]
      have he : LongestPathWork.rowValues measuredWidth.value.access.active = width.final.rows.active :=
        funext (fun u => funext (measuredWidth.value.access.active_value u))
      rw [he, rank_eq]
      rfl
    let length := FiniteLoopWork.length path.value
    if hlong : p.H ≤ length.value then
      have hlong' : p.H ≤ (longestChain width.final.rows.active graph.rank p.scale.H).length := by
        simpa only [length, FiniteLoopWork.length_value, path_eq] using hlong
      let prefixResult := LongestPathWork.take p.H path.value
      have prefix_eq : prefixResult.value = reserve width.final.rows.active graph.rank p.scale.H p.H := by
        simp only [prefixResult, LongestPathWork.take_value, path_eq, SparseRepairGraph.reserve]
      let reservation := reservationFrom width.final p graph hlong' prefixResult.value prefix_eq
      let group := MeasuredPath.run widthExecutor p ordinaryExecutor width.final width.final reservation
        reservation.labels (fun _ h => h) (Context.refl _) graph width.bound
        measuredWidth.value.access measuredWidth.value.cached
      let rest := normalize widthExecutor p ordinaryExecutor group.value.result.final
        (group.value.result.trace.sparseBounds graph) group.value.result.bound
        group.value.access group.value.cached rank rank_eq
      let result := pathResult s p width selected reservation group.value.result rest.value.result
      ⟨⟨result, rest.value.access,
        path_actual s p g hB width measuredWidth.value.actual selected hlong' reservation
          (reservationFrom_actual ..) group.value.result group.value.actual rest.value.result rest.value.actual,
        rest.value.cached⟩,
        measuredWidth.work + degree.work + path.work + length.work + prefixResult.work + group.work + rest.work +
          2 * (width.trace.length + group.value.result.trace.length) + 16⟩
    else
      have hlong' : ¬ p.H ≤ (longestChain width.final.rows.active graph.rank p.scale.H).length := by
        simpa only [length, FiniteLoopWork.length_value, path_eq] using hlong
      let result := finishResult s p g width selected hlong'
      ⟨⟨result, measuredWidth.value.access,
        finish_actual s p g hB width measuredWidth.value.actual selected hlong', measuredWidth.value.cached⟩,
        measuredWidth.work + degree.work + path.work + length.work + 6⟩
termination_by s.measure
decreasing_by
  all_goals
    have hwidth : width.final.measure ≤ s.measure := by
      have h := width.trace.length_add_measure_le
      omega
  · exact ordinary.update.measure_lt.trans_le hwidth
  · have hgroup : group.value.result.final.measure < width.final.measure := by
      rw [group.value.actual]
      exact executePath_measure_lt width.final p reservation graph width.bound
    exact hgroup.trans_le hwidth

end SortingAdversary.Optimal.MeasuredStructuralNormalize
