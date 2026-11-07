import SortingAdversary.Optimal.MeasuredStopContext
import SortingAdversary.Optimal.UniformPreparedWork
import SortingAdversary.Optimal.MeasuredOracleBounds

/-!
# The actual counted stopping program for an accepted uniform stage

The sign, physical comparison, compressed rank, complete repair and tree
replay are all computed by their measured implementations. Only their
observable tree, answer and allocator fields are retained. The proof context
contains the original program solely in erased specifications.
-/

namespace SortingAdversary.Optimal.UniformStopWork

open PrimitiveWork WidthRepair PoolState PoolTree.Tree StoredRouting RecursiveController
open LocalOracle RepresentationWork MeasuredController MeasuredStop UniformStage

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {n j : ℕ}

/-- Build the sparse certificate from the already computed rank vector.
The original rank program is never an executable field of this record. -/
def computedGraph (a : Accepted (Parameters.logCap n) j) (c : Context a.controller n)
    (sign : c.Sign) (state : State n) (actual : state = c.next sign)
    (ranks : Vector ℕ n)
    (ranks_eq : ranks = Vector.ofFn (SparseRepairGraph.rankAfterAdd c.before.rows.active
      (NormalizedBounds.rank c.before) a.controller.repair.H (c.second sign))) :
    SparseBounds state.rows a.controller.repair.scale.H a.controller.repair.d := by
  have hr : (fun x => ranks[x]) = (Context.castGraph actual (c.graph sign)).rank := by
    rw [Context.castGraph_rank, ranks_eq]
    funext x
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rfl
  exact {
    rank := fun x => ranks[x]
    strict := by
      intro x y h
      rw [congrFun hr x, congrFun hr y]
      exact (Context.castGraph actual (c.graph sign)).strict x y h
    height := by
      intro x
      rw [congrFun hr x]
      exact (Context.castGraph actual (c.graph sign)).height x
    degree := (Context.castGraph actual (c.graph sign)).degree }

theorem computedGraph_eq (a : Accepted (Parameters.logCap n) j) (c : Context a.controller n)
    (sign : c.Sign) (state : State n) (actual : state = c.next sign)
    (ranks : Vector ℕ n)
    (ranks_eq : ranks = Vector.ofFn (SparseRepairGraph.rankAfterAdd c.before.rows.active
      (NormalizedBounds.rank c.before) a.controller.repair.H (c.second sign))) :
    computedGraph a c sign state actual ranks ranks_eq = Context.castGraph actual (c.graph sign) := by
  apply Context.sparseBounds_ext
  rw [Context.castGraph_rank]
  change (fun x => ranks[x]) = _
  rw [ranks_eq]
  funext x
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

def leaf (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a)
    (c : Context a.controller n) (access : LocalAccess c.before) (cached : AccessBound access 2)
    (children : ChildrenAccess c.children) (children_cached : children.Bound 2) (counter : ℕ) :
    Result (Output (Core.ofAnswered (c.reference counter))) :=
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
  let packed := TreeAccess.pack c.identity replay.value.access replay.value.state.pool.palette
    replay.value.state.pool.members rfl rfl replay.value.nextAccess
  let core : Core n := ⟨sign.forward, packed.value.stored, replay.value.nextCounter⟩
  have actual : core = Core.ofAnswered (c.reference counter) := by
    have hpack : packed.value.stored =
        StoredRepair.node c.identity normalized.value.result.final replay.value.nextChildren := by
      rw [packed.value.stored_eq, replay.value.state_eq]
      rfl
    change (⟨sign.forward, packed.value.stored, replay.value.nextCounter⟩ : Core n) = _
    rw [hpack]
    exact c.completed_actual counter sign choice.value.actual comparison.value.state comparison.value.actual
      graph (computedGraph_eq ..) comparable normalized.value.result normalized.value.actual hw ho
      replay.value.nextChildren replay.value.children_eq replay.value.nextCounter replay.value.counter_eq
  ⟨⟨core, packed.value.rebased, actual,
    packed.value.rebased_bound (TreeAccess.pack_bound _ _ _ _ _ _ _
      replay.value.cached replay.value.children_cached)⟩,
    choice.work + comparison.work + ranks.work + normalized.work + replay.work + packed.work + 30⟩

/-- No counting, repair, replay or routing callback remains in this leaf. -/
def executor (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a) :
    StopExecutor (RecursiveController.stop (n := n) a.controller) :=
  fun t access cached hw ho normal x y hx hy hxy hyx hstop counter => by
    cases access with
    | @node identity q d root children represented =>
      let context : Context a.controller n :=
        ⟨identity, PassiveLocalState.state q d, children, hw, ho, normal, x, y, hx, hy, hxy, hyx, hstop⟩
      exact leaf a data context root cached.1 represented cached.2 counter

end SortingAdversary.Optimal.UniformStopWork
