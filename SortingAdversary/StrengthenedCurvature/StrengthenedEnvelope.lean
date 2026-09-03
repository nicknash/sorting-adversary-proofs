import SortingAdversary.StrengthenedCurvature.StrengthenedBranchBounds
import SortingAdversary.StrengthenedCurvature.RhoConvexity

/-!
# Exact two-variable strengthened envelope reduction

The averaging parameter is a proof witness only.  The deterministic
adversary still evaluates the two explicit child trial points and chooses
the smaller one.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

set_option maxHeartbeats 2000000

/-- Equations (50), (54), and (57): the smaller trial branch is bounded by
the two-variable scalar envelope. -/
theorem min_trial_scaledLogDet_le_scalarEnvelope
    {n : ℕ} {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (q : Query n)
    {delta a b lambda : ℝ}
    (hdelta : delta = queryOffset h x (centerOrientation x q))
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hcross : delta < b) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    let o := centerOrientation x q
    let motion := electricalNormalizedMotions h x o hc.1
    min
      (scaledLogDet (augmentedRows h x o (delta + a))
          (augmentedMotions h x o) a -
        Real.log (barrierHessian h x).det)
      (scaledLogDet (augmentedRows h x o (b - delta))
          (augmentedMotions h x o) (-b) -
        Real.log (barrierHessian h x).det) ≤
      scalarEnvelope delta motion.positiveEnergy a b lambda := by
  dsimp only
  let o := centerOrientation x q
  let motion := electricalNormalizedMotions h x o hc.1
  have hplus := positive_scaledLogDet_bound_strengthened hc o
    (centerOrientation_slack_nonneg x q) hdelta ha0 ha1
  have hminus := negative_scaledLogDet_bound_strengthened hc o hdelta
    hb0 hb1 hcross
  have hframe := normalizedMotions_endpoint_reduction motion delta a b lambda
    ha0.le ha1 hb0.le hb1 hl0 hl1
  have hweighted := min_le_weighted_average (x :=
      Real.log (1 + 1 / (delta + a) ^ 2) +
        ∑ i : OldRowIndex h,
          phiPlus delta a
            (electricalMotion h x o (indexedBarrierRow h i)) -
        gammaPlus a motion.positiveEnergy) (y :=
      Real.log (1 + 1 / (b - delta) ^ 2) +
        ∑ i : OldRowIndex h,
          phiMinus delta b
            (electricalMotion h x o (indexedBarrierRow h i)) -
        gammaMinus b motion.positiveEnergy) hl0 hl1
  calc
    min
      (scaledLogDet (augmentedRows h x o (delta + a))
          (augmentedMotions h x o) a -
        Real.log (barrierHessian h x).det)
      (scaledLogDet (augmentedRows h x o (b - delta))
          (augmentedMotions h x o) (-b) -
        Real.log (barrierHessian h x).det) ≤
        min
          (Real.log (1 + 1 / (delta + a) ^ 2) +
            ∑ i : OldRowIndex h,
              phiPlus delta a
                (electricalMotion h x o (indexedBarrierRow h i)) -
            gammaPlus a motion.positiveEnergy)
          (Real.log (1 + 1 / (b - delta) ^ 2) +
            ∑ i : OldRowIndex h,
              phiMinus delta b
                (electricalMotion h x o (indexedBarrierRow h i)) -
            gammaMinus b motion.positiveEnergy) :=
      min_le_min hplus hminus
    _ ≤ lambda *
          (Real.log (1 + 1 / (delta + a) ^ 2) +
            ∑ i : OldRowIndex h,
              phiPlus delta a
                (electricalMotion h x o (indexedBarrierRow h i)) -
            gammaPlus a motion.positiveEnergy) +
        (1 - lambda) *
          (Real.log (1 + 1 / (b - delta) ^ 2) +
            ∑ i : OldRowIndex h,
              phiMinus delta b
                (electricalMotion h x o (indexedBarrierRow h i)) -
            gammaMinus b motion.positiveEnergy) := hweighted
    _ = lambda * Real.log (1 + 1 / (delta + a) ^ 2) +
          (1 - lambda) * Real.log (1 + 1 / (b - delta) ^ 2) +
          ∑ i : OldRowIndex h,
            phiAverage delta a b lambda
              (electricalMotion h x o (indexedBarrierRow h i)) -
          lambda * gammaPlus a motion.positiveEnergy -
          (1 - lambda) * gammaMinus b motion.positiveEnergy := by
      simp only [phiAverage]
      rw [mul_sub, mul_sub, mul_add, mul_add, Finset.mul_sum,
        Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ ≤ lambda * Real.log (1 + 1 / (delta + a) ^ 2) +
          (1 - lambda) * Real.log (1 + 1 / (b - delta) ^ 2) +
          (motion.positiveEnergy *
              positiveEndpointMax delta motion.positiveEnergy a b lambda +
            (1 - motion.positiveEnergy) *
              negativeEndpointMax delta motion.positiveEnergy a b lambda) -
          lambda * gammaPlus a motion.positiveEnergy -
          (1 - lambda) * gammaMinus b motion.positiveEnergy := by
      have hframe' :
          (∑ i : OldRowIndex h,
            phiAverage delta a b lambda
              (electricalMotion h x o (indexedBarrierRow h i))) ≤
            motion.positiveEnergy *
                positiveEndpointMax delta motion.positiveEnergy a b lambda +
              (1 - motion.positiveEnergy) *
                negativeEndpointMax delta motion.positiveEnergy a b lambda := by
        simpa only [motion, electricalNormalizedMotions] using hframe
      linarith
    _ = scalarEnvelope delta motion.positiveEnergy a b lambda := by
      unfold scalarEnvelope
      ring

end StrengthenedCurvature
end SortingAdversary
