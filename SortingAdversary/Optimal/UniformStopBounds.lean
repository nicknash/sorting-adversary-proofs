import SortingAdversary.Optimal.UniformStopWork
import SortingAdversary.Optimal.UniformRepairPolynomial

/-! # A fixed polynomial bound for the complete counted stopping program -/

namespace SortingAdversary.Optimal.UniformStopWork

open PrimitiveWork WidthRepair PoolState PoolTree.Tree StoredRouting RecursiveController
open LocalOracle RepresentationWork MeasuredController MeasuredStop UniformStage

set_option maxRecDepth 8192
set_option maxHeartbeats 600000

variable {n j : ℕ}

def bound (n : ℕ) : ℕ :=
  StoppingTestsWork.workBound n 2 + 2 * MeasuredOracleBudget.branchPolynomial n (2 * n) 4 2 +
    LocalAccess.cacheBound n (2 * n + 1) 16 + ComparedWork.rankBound n 2 +
    1000000000000 * (n + 1) ^ 15 + (n + n * n) * (TreeReplay.stepBound n + 20) + 200

theorem leaf_work (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a)
    (c : Context a.controller n) (access : LocalAccess c.before) (cached : AccessBound access 2)
    (children : ChildrenAccess c.children) (children_cached : children.Bound 2) (counter : ℕ)
    (hb : PoolPalette.TreeBounded c.node.erase) :
    (leaf a data c access cached children children_cached counter).work ≤ bound n := by
  let choice := MeasuredStopping.atRadius access a.controller c.localReady c.x c.y c.hxy c.hyx c.hstop
    data.comparisonRadius data.comparison_exact
  let sign := choice.value.sign
  let comparison := ComparedWork.compare access (c.first sign) (c.second sign)
    (c.first_member sign) (c.second_member sign) (c.distinct sign) (c.updated sign)
    c.before.pool.palette c.before.pool.members rfl rfl
  let ranks := ComparedWork.afterRank access a.controller.repair.H (c.second sign)
  let graph := computedGraph a c sign comparison.value.state comparison.value.actual ranks.value
    (ComparedWork.afterRank_value access _ _)
  have comparable := Context.castComparable comparison.value.actual (c.comparable sign)
  let normalized := UniformRepairWork.atRadius a data.repair comparison.value.state graph comparable
    comparison.value.access comparison.value.cached (fun x => ⟨ranks.value[x], 1⟩) rfl
  have hw : (StoredRepair.node c.identity comparison.value.state c.children).erase.WellFormed := by
    rw [comparison.value.actual]
    exact c.next_wellFormed sign
  have ho : (StoredRepair.node c.identity comparison.value.state c.children).erase.Coherent := by
    rw [comparison.value.actual]
    exact c.next_coherent sign
  let replay := TreeReplay.run c.identity normalized.value.result.trace comparison.value.access children
    comparison.value.cached children_cached hw ho counter
  have hp : c.before.pool.palette ≤ 2 * n + 1 := by
    have h := stored_palette_size c.node hb
    change c.before.pool.palette + 1 ≤ 2 * n + 2 at h
    omega
  have hn : n ≠ 0 := Nat.ne_of_gt (UniformScalarWork.input_pos a)
  have hchoice := MeasuredOracleBounds.stopping_work_of_radius_logCap access cached a.controller
    c.localReady c.x c.y c.hxy c.hyx c.hstop data.comparisonRadius data.comparison_exact
    4 hn a.comparisonBall_cap (by omega : c.before.pool.palette + 1 ≤ 4 * n)
  have hcompare := ComparedWork.compare_work_le access cached (c.first sign) (c.second sign)
    (c.first_member sign) (c.second_member sign) (c.distinct sign) (c.updated sign)
    c.before.pool.palette c.before.pool.members rfl rfl
  have hcache : LocalAccess.cacheBound n c.before.pool.palette (3 * 2 + 10) ≤
      LocalAccess.cacheBound n (2 * n + 1) 16 := by
    change LocalAccess.cacheBound n c.before.pool.palette 16 ≤ LocalAccess.cacheBound n (2 * n + 1) 16
    unfold LocalAccess.cacheBound
    gcongr
  have hrank := ComparedWork.afterRank_work_le access cached a.controller.repair.H (c.second sign)
  have hpalette : comparison.value.state.pool.palette ≤ 2 * n + 1 := by
    rw [comparison.value.actual]
    exact hp
  have hnormal := UniformRepairWork.atRadius_work_le a data.repair comparison.value.state graph comparable
    comparison.value.access comparison.value.cached (fun x => ⟨ranks.value[x], 1⟩) rfl
    (fun _ => Nat.le_succ 1) (UniformRepairWork.localCap n) (UniformRepairWork.size_le_localCap hpalette)
  have hpoly : UniformRepairWork.repairBound n (UniformRepairWork.localCap n) ≤
      1000000000000 * (n + 1) ^ 15 := by
    apply Nat.le_trans _ (UniformRepairWork.polynomial_le n)
    unfold UniformRepairWork.polynomial
    omega
  have hbounded : PoolPalette.TreeBounded (StoredRepair.node c.identity comparison.value.state c.children).erase := by
    rw [comparison.value.actual]
    exact c.next_bounded sign hb
  have hreplay := TreeReplay.run_work c.identity normalized.value.result.trace comparison.value.access children
    comparison.value.cached children_cached hw ho counter hbounded
  have hlength := MeasuredRepairBounds.trace_length_le normalized.value.result.trace
  have htrace : normalized.value.result.trace.length * (TreeReplay.stepBound n + 20) ≤
      (n + n * n) * (TreeReplay.stepBound n + 20) := Nat.mul_le_mul_right _ hlength
  change choice.work + comparison.work + ranks.work + normalized.work + replay.work + 40 + 30 ≤ bound n
  change choice.work ≤ _ at hchoice
  change comparison.work ≤ _ at hcompare
  change ranks.work ≤ _ at hrank
  change normalized.work ≤ _ at hnormal
  change replay.work ≤ _ at hreplay
  unfold bound
  omega

theorem executor_work (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a)
    (t : StoredTree n) (access : TreeAccess t) (cached : access.Bound 2)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (normal : AllNodes (ready a.controller) t)
    (x y : Fin n) (hx : x ∈ t.pool.members) (hy : y ∈ t.pool.members)
    (hxy : t.pool.system.edge x y ≠ true) (hyx : t.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins x = some c ∧ t.pool.pins y = some c) (counter : ℕ)
    (hb : PoolPalette.TreeBounded t.erase) :
    (executor a data t access cached hw ho normal x y hx hy hxy hyx hstop counter).work ≤ bound n := by
  cases access with
  | @node identity q d root children represented =>
    let context : Context a.controller n :=
      ⟨identity, PassiveLocalState.state q d, children, hw, ho, normal, x, y, hx, hy, hxy, hyx, hstop⟩
    change (leaf a data context root cached.1 represented cached.2 counter).work ≤ bound n
    exact leaf_work a data context root cached.1 represented cached.2 counter hb

end SortingAdversary.Optimal.UniformStopWork
