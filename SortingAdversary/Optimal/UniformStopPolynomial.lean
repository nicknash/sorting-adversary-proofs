import SortingAdversary.Optimal.UniformStopBounds

namespace SortingAdversary.Optimal.UniformStopWork

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bound_polynomial (n : ℕ) : bound n ≤ 2000000000000 * (n + 1) ^ 15 := by
  unfold bound StoppingTestsWork.workBound StoppingTestsWork.windowsBound StoppingTestsWork.innerBound
    MeasuredOracleBudget.branchPolynomial MeasuredLocalOracle.prepareBound MeasuredLocalOracle.labelsBound
    MeasuredLocalOracle.oneCountBound LocalDPWork.polynomialBound LocalDPWork.baseBound
    LocalDPWork.layerBound LocalDPWork.predicateBound ScaleWalksWork.reachBound
    ScaleWalksWork.baseBound ScaleWalksWork.layerBound ComparedWork.rankBound
    RankWork.workBound LongestPathWork.tableBound ClosureWork.workBound
    RepresentationWork.TreeReplay.stepBound RepresentationWork.LocalAccess.updateBound
    RepresentationWork.TreeAccess.promotionBound RepresentationWork.TreeAccess.admissionBound
    RepresentationWork.treeShapeBound RepresentationWork.LocalAccess.cacheBound WindowWork.endpointWorkBound
  ring_nf
  gcongr <;> norm_num

end SortingAdversary.Optimal.UniformStopWork
