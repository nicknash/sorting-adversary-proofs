import SortingAdversary.Optimal.UniformRepairWork
import SortingAdversary.Optimal.MeasuredOracleBounds
import Mathlib.Tactic.Ring

/-! Fixed-exponent envelopes for the executed uniform repair and its local counts. -/

namespace SortingAdversary.Optimal.UniformRepairWork

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A deliberately loose degree-fifteen bound for the explicit polynomial
already proved to dominate every executed repair loop. -/
theorem polynomial_le (n : ℕ) : polynomial n ≤ 1000000000000 * (n + 1) ^ 15 := by
  unfold polynomial repairBound localCap MeasuredStructuralNormalize.kernelBound
    MeasuredPath.workBound LongestPathWork.chainBound LongestPathWork.tableBound
    SelectorWork.degreeWorkBound ordinaryBound MeasuredOrdinaryPromotion.workBound
    MeasuredOrdinaryPromotion.chooseBound CalibrationWork.firstBound HubWork.windowPolynomial
    MeasuredOracleBudget.cdfPolynomial MeasuredLocalOracle.prepareBound
    MeasuredLocalOracle.labelsBound MeasuredLocalOracle.oneCountBound LocalDPWork.polynomialBound
    LocalDPWork.baseBound LocalDPWork.layerBound LocalDPWork.predicateBound
    WidthPolynomialWork.bound WidthPolynomialWork.kernel WidthPolynomialWork.early
    WidthPolynomialWork.group WidthPolynomialWork.plan WidthPolynomialWork.vertices
    ScaleVerticesWork.pathBound ScaleVerticesWork.selectedBound ScaleCrossingWork.firstBound
    ScaleBlocksWork.workBound ScaleBlocksWork.entryBound HubWork.groupPolynomial
    RepairSelectWork.earlyBound RepairSelectWork.scaleBound RepairSelectWork.widthBound
    CentralChoiceWork.workBound SelectorWork.narrowWorkBound SelectorWork.steepWorkBound
    SelectorWork.neighborWorkBound MeasuredPin.workBound RepresentationWork.LocalAccess.cacheBound
    WindowWork.endpointWorkBound ScaleWalksWork.distanceBound ScaleWalksWork.walkBound
    ScaleWalksWork.reachBound ScaleWalksWork.baseBound ScaleWalksWork.layerBound
  ring_nf
  gcongr <;> norm_num

theorem local_countBits_le (n : ℕ) :
    MeasuredOracleBounds.countBits n (localCap n + 1) ≤ 30 * (n + 1) ^ 4 := by
  unfold MeasuredOracleBounds.countBits localCap
  ring_nf
  gcongr <;> norm_num

/-- This bound includes exact equality with the reference structural repair;
it is a bound on the actual counted implementation, not on a separate schedule. -/
theorem normalize_work_polynomial {n j : ℕ} (a : UniformStage.Accepted (Parameters.logCap n) j)
    (s : WidthRepair.State n)
    (g : LocalOracle.SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : WidthRepair.ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : RepresentationWork.LocalAccess s) (cached : RepresentationWork.AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank)
    (hrank : ∀ v, (rank v).work ≤ 2) (hpalette : s.pool.palette ≤ 2 * n + 1) :
    (normalize a s g hB access cached rank rank_eq).work ≤ 1000000000000 * (n + 1) ^ 15 :=
  (normalize_work_le a s g hB access cached rank rank_eq hrank hpalette).trans (polynomial_le n)

end SortingAdversary.Optimal.UniformRepairWork
