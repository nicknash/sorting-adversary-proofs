import SortingAdversary.Optimal.MeasuredStructuralNormalize

/-! Polynomial composition for the measured outer repair loop. -/

namespace SortingAdversary.Optimal.MeasuredStructuralNormalize

open WidthRepair StructuralNormalize RepresentationWork LocalOracle PoolState
open SparseRepairGraph GraphBalls MeasuredRepairBounds

set_option maxRecDepth 8192

variable {n : ℕ}

def kernelBound (n height rankWork widthWork ordinaryWork : ℕ) : ℕ :=
  widthWork + ordinaryWork + SelectorWork.degreeWorkBound n 2 3 +
    LongestPathWork.chainBound n height 2 rankWork +
    MeasuredPath.workBound n n widthWork ordinaryWork + 4 * (n + n * n) + 5 * n + 40

theorem normalize_work_le (widthExecutor : MeasuredWidthNormalize.Executor n) (p : Parameters)
    (ordinaryExecutor : MeasuredOrdinaryPromotion.Executor n p.scale.H p.d p.scale.R)
    (cap widthWork ordinaryWork rankWork : ℕ)
    (hwidth : WidthBound widthExecutor p.scale p.d cap widthWork)
    (hordinary : OrdinaryBound p ordinaryExecutor cap ordinaryWork)
    (s : State n) (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank)
    (hrank : ∀ v, (rank v).work ≤ rankWork) (hsize : size s ≤ cap) :
    (normalize widthExecutor p ordinaryExecutor s g hB access cached rank rank_eq).work ≤
      (s.measure + 1) * kernelBound n p.scale.H rankWork widthWork ordinaryWork := by
  let measuredWidth := widthExecutor access cached p.scale p.d g hB
  let width := measuredWidth.value.result
  let graph := width.trace.sparseBounds g
  let degree := RepairSelectWork.degree measuredWidth.value.access p.D
  have hw : measuredWidth.work ≤ widthWork := hwidth access cached g hB hsize
  have hs : size width.final ≤ cap := (trace_size_le width.trace).trans hsize
  have hl : width.trace.length ≤ n + n * n := trace_length_le width.trace
  have hm : width.final.measure ≤ s.measure := by
    have := width.trace.length_add_measure_le
    omega
  have hd : degree.work ≤ SelectorWork.degreeWorkBound n 2 3 :=
    RepairSelectWork.degree_work_le measuredWidth.value.access measuredWidth.value.cached p.D
  rw [normalize]
  dsimp only
  split
  · rename_i v hselected
    have selected : degreeWitness width.final.rows.active width.final.pool.free p.D = some v :=
      (RepairSelectWork.degree_value measuredWidth.value.access p.D).symm.trans hselected
    let hs' := degreeWitness_some width.final.rows.active width.final.pool.free p.D selected
    let incident : (neighbors width.final.rows.active v).Nonempty :=
      Finset.card_pos.mp (p.degree_pos.trans_le hs'.2)
    let measuredOrdinary := ordinaryExecutor measuredWidth.value.access measuredWidth.value.cached
      graph (by positivity) v (width.normal.markCondition p.d (1 / 16) p.minimum v)
      ((width.final.pool.free_iff v).mp hs'.1) (width.final.nonisolated_mate incident)
    let ordinary := measuredOrdinary.value.result
    let one := MeasuredPath.one ordinary
    have ho : measuredOrdinary.work ≤ ordinaryWork :=
      hordinary measuredWidth.value.access measuredWidth.value.cached graph v
        (width.normal.markCondition p.d (1 / 16) p.minimum v)
        ((width.final.pool.free_iff v).mp hs'.1) (width.final.nonisolated_mate incident) hs
    have hnext : ordinary.update.next.measure < s.measure := ordinary.update.measure_lt.trans_le hm
    have ht := normalize_work_le widthExecutor p ordinaryExecutor cap widthWork ordinaryWork rankWork
      hwidth hordinary ordinary.update.next (one.sparseBounds graph)
      (comparableBound_trace one width.bound) measuredOrdinary.value.access measuredOrdinary.value.cached
      rank rank_eq hrank ((pin_size_le ordinary.update).trans hs)
    have ht' := ht.trans (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hnext))
    change measuredWidth.work + degree.work + measuredOrdinary.work +
      (normalize widthExecutor p ordinaryExecutor ordinary.update.next (one.sparseBounds graph) _
        measuredOrdinary.value.access measuredOrdinary.value.cached rank rank_eq).work +
      2 * width.trace.length + 12 ≤ _
    simp only [Nat.add_mul, Nat.one_mul]
    have hlocal : measuredWidth.work + degree.work + measuredOrdinary.work + 2 * width.trace.length + 12 ≤
        kernelBound n p.scale.H rankWork widthWork ordinaryWork := by
      unfold kernelBound
      omega
    omega
  · rename_i hselected
    let path := LongestPathWork.longestChain measuredWidth.value.access.active rank p.scale.H
    have he : LongestPathWork.rowValues measuredWidth.value.access.active = width.final.rows.active :=
      funext (fun u => funext (measuredWidth.value.access.active_value u))
    have hstrict : ∀ u v, Arc (LongestPathWork.rowValues measuredWidth.value.access.active) u v →
        LongestPathWork.rankValues rank u < LongestPathWork.rankValues rank v := by
      rw [he, rank_eq]
      exact graph.strict
    have hp : path.work ≤ LongestPathWork.chainBound n p.scale.H 2 rankWork :=
      LongestPathWork.longestChain_work_le _ _ _ _ _ measuredWidth.value.cached.active hrank hstrict
    have hplen : path.value.length ≤ n := LongestPathWork.longestChain_length_le _ _ _ hstrict
    have path_eq : path.value = longestChain width.final.rows.active graph.rank p.scale.H := by
      rw [LongestPathWork.longestChain_value, he, rank_eq]
      rfl
    let length := FiniteLoopWork.length path.value
    have hlength : length.work ≤ 2 * n + 1 := by
      simp only [length, FiniteLoopWork.length_work]
      omega
    split
    · rename_i hlong
      have hlong' : p.H ≤ (longestChain width.final.rows.active graph.rank p.scale.H).length := by
        have h := hlong
        change p.H ≤ (FiniteLoopWork.length path.value).value at h
        rw [FiniteLoopWork.length_value, path_eq] at h
        exact h
      let prefixResult := LongestPathWork.take p.H path.value
      have prefix_eq : prefixResult.value = reserve width.final.rows.active graph.rank p.scale.H p.H := by
        simp only [prefixResult, LongestPathWork.take_value, path_eq, SparseRepairGraph.reserve]
      let reservation := reservationFrom width.final p graph hlong' prefixResult.value prefix_eq
      let group := MeasuredPath.run widthExecutor p ordinaryExecutor width.final width.final reservation
        reservation.labels (fun _ h => h) (Context.refl _) graph width.bound
        measuredWidth.value.access measuredWidth.value.cached
      have hreservation : reservation.labels.length ≤ n := by
        simpa only [Fintype.card_fin] using reservation.nodup.length_le_card
      have hprefix : prefixResult.work ≤ 3 * n + 1 :=
        (LongestPathWork.take_work_le p.H path.value).trans (by omega)
      have hgroup := MeasuredPath.run_work_le widthExecutor p ordinaryExecutor cap widthWork ordinaryWork
        hwidth hordinary width.final width.final reservation reservation.labels (fun _ h => h)
        (Context.refl _) graph width.bound measuredWidth.value.access measuredWidth.value.cached hs
      have hgroup' : group.work ≤ MeasuredPath.workBound n n widthWork ordinaryWork := by
        apply hgroup.trans
        unfold MeasuredPath.workBound
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hreservation) 1
      have hgroupSize : size group.value.result.final ≤ cap := (trace_size_le group.value.result.trace).trans hs
      have hgroupLength : group.value.result.trace.length ≤ n + n * n := trace_length_le group.value.result.trace
      have hnext : group.value.result.final.measure < s.measure := by
        have hg : group.value.result.final.measure < width.final.measure := by
          rw [group.value.actual]
          exact executePath_measure_lt width.final p reservation graph width.bound
        exact hg.trans_le hm
      have ht := normalize_work_le widthExecutor p ordinaryExecutor cap widthWork ordinaryWork rankWork
        hwidth hordinary group.value.result.final (group.value.result.trace.sparseBounds graph)
        group.value.result.bound group.value.access group.value.cached rank rank_eq hrank hgroupSize
      have ht' := ht.trans (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hnext))
      change measuredWidth.work + degree.work + path.work + length.work + prefixResult.work + group.work +
        (normalize widthExecutor p ordinaryExecutor group.value.result.final
          (group.value.result.trace.sparseBounds graph) group.value.result.bound
          group.value.access group.value.cached rank rank_eq).work +
        2 * (width.trace.length + group.value.result.trace.length) + 16 ≤ _
      simp only [Nat.add_mul, Nat.one_mul]
      have hlocal : measuredWidth.work + degree.work + path.work + length.work + prefixResult.work + group.work +
          2 * (width.trace.length + group.value.result.trace.length) + 16 ≤
          kernelBound n p.scale.H rankWork widthWork ordinaryWork := by
        unfold kernelBound
        omega
      omega
    · change measuredWidth.work + degree.work + path.work + length.work + 6 ≤ _
      have hlocal : measuredWidth.work + degree.work + path.work + length.work + 6 ≤
          kernelBound n p.scale.H rankWork widthWork ordinaryWork := by
        unfold kernelBound
        omega
      exact hlocal.trans (by
        simpa only [Nat.one_mul] using
          (Nat.mul_le_mul_right (kernelBound n p.scale.H rankWork widthWork ordinaryWork)
            (Nat.le_add_left 1 s.measure)))
termination_by s.measure
decreasing_by
  all_goals assumption

end SortingAdversary.Optimal.MeasuredStructuralNormalize
