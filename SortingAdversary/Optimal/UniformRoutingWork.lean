import SortingAdversary.Optimal.MeasuredRoutingWork
import SortingAdversary.Optimal.MeasuredActive
import SortingAdversary.Optimal.UniformStopPolynomial

/-!
# The concrete counted recursive answer program

An accepted stage supplies the measured stopping leaf. The stored-tree
router then has no oracle, repair, routing or representation callback left
to implement. Its result certifies the exact original answer, updated tree
and allocator counter.
-/

namespace SortingAdversary.Optimal.UniformRoutingWork

open RepresentationWork MeasuredController UniformStage RecursiveController

variable {n j : ℕ}

def executor (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a) :
    AnswerExecutor a.controller n :=
  MeasuredController.route (RecursiveController.stop a.controller)
    (PassiveLocalState.ready_delegation_stable a.controller.repair.scale a.controller.repair.D a.controller.repair.H)
    (fun _ _ _ record => record) (UniformStopWork.executor a data)

def bound (n : ℕ) : ℕ :=
  (n + 1) * routingNodeBound n (UniformStopWork.bound n) + 2

theorem executor_bound (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a) :
    AnswerBound (executor a data) (bound n) := by
  intro t access cached hw ho normal x y hx hy hxy hyx counter hb
  exact MeasuredController.route_work _ _ _ (UniformStopWork.executor a data) (UniformStopWork.bound n)
    (UniformStopWork.executor_work a data) t access cached hw ho normal x y hx hy hxy hyx counter hb

theorem bound_polynomial (n : ℕ) : bound n ≤ 3000000000000 * (n + 1) ^ 16 := by
  have hs := UniformStopWork.bound_polynomial n
  unfold bound routingNodeBound
  calc
    (n + 1) * (UniformStopWork.bound n + LocalAccess.cacheBound n (treeShapeBound n) 16 +
        44 * treeShapeBound n + 140) + 2 ≤
      (n + 1) * (2000000000000 * (n + 1) ^ 15 + LocalAccess.cacheBound n (treeShapeBound n) 16 +
        44 * treeShapeBound n + 140) + 2 := by gcongr
    _ ≤ 3000000000000 * (n + 1) ^ 16 := by
      unfold LocalAccess.cacheBound treeShapeBound
      ring_nf
      gcongr <;> norm_num

theorem executor_polynomial (a : Accepted (Parameters.logCap n) j) (data : UniformPreparedWork.Data a) :
    AnswerBound (executor a data) (3000000000000 * (n + 1) ^ 16) := by
  intro t access cached hw ho normal x y hx hy hxy hyx counter hb
  exact (executor_bound a data t access cached hw ho normal x y hx hy hxy hyx counter hb).trans (bound_polynomial n)

end SortingAdversary.Optimal.UniformRoutingWork
