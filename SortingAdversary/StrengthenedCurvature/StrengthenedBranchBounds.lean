import SortingAdversary.StrengthenedCurvature.BranchBounds
import SortingAdversary.StrengthenedCurvature.RateSaving

/-!
# Trial-branch bounds with the sign-imbalance saving retained

These are equations (45) and (47) of the strengthened-curvature note.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open Set intervalIntegral
open scoped BigOperators

set_option maxHeartbeats 2000000

variable {n : ℕ}

/-- Equation (45), including the certified `Γ₊` saving. -/
theorem positive_scaledLogDet_bound_strengthened {h : History n}
    {x : Placement n} (hc : IsVolumetricCenter h x) (o : Observation n)
    {delta a : ℝ} (ho : 0 ≤ (BarrierRow.ofObservation o).slack x)
    (hdelta : delta = queryOffset h x o) (ha0 : 0 < a) (ha1 : a < 1) :
    scaledLogDet (augmentedRows h x o (delta + a))
          (augmentedMotions h x o) a -
        Real.log (barrierHessian h x).det ≤
      Real.log (1 + 1 / (delta + a) ^ 2) +
        ∑ i : OldRowIndex h,
          phiPlus delta a
            (electricalMotion h x o (indexedBarrierRow h i)) -
        gammaPlus a
          (electricalNormalizedMotions h x o hc.1).positiveEnergy := by
  subst delta
  let motion := electricalNormalizedMotions h x o hc.1
  have ht : queryOffset h x o + a ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (queryOffset_nonneg hc.1 ho) ha0)
  have hcurve := scaledLogDet_endpoint_sub_tangent_le_strengthened
    (V := augmentedRows h x o (queryOffset h x o + a))
    (d := augmentedMotions h x o) ha0
    (fun s hs => augmented_rowDenominator_ne hc.1 o (by
      rw [abs_of_nonneg hs.1]
      exact hs.2.trans_lt ha1))
    (fun s hs => scaledGram_augmented_det_pos hc.1 o _ (by
      rw [abs_of_nonneg hs.1]
      exact hs.2.trans_lt ha1))
  have hintegral :
      (∫ s in (0 : ℝ)..a, (a - s) *
          scaledRateGap (augmentedMotions h x o) s ^ 2) =
        ∫ s in (0 : ℝ)..a, (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le ha0.le] using hs
    change (a - s) * scaledRateGap (augmentedMotions h x o) s ^ 2 =
      (a - s) * (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2
    rw [scaledRateGap_augmented_eq o hc.1 hs'.1 (hs'.2.trans_lt ha1)]
  rw [hintegral] at hcurve
  have hgamma := motion.gammaPlus_le_integratedRateGap ha0.le ha1
  have hcurveSave :
      scaledLogDet
            (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) a -
          scaledLogDet
            (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) 0 -
          a * scaledLogDetFirst
            (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) 0 ≤
        rowCurvatureSum (augmentedMotions h x o) a -
          gammaPlus a motion.positiveEnergy := by
    linarith
  have hzero := scaledLogDet_zero_sub_old hc.1 o ht
  calc
    scaledLogDet (augmentedRows h x o (queryOffset h x o + a))
          (augmentedMotions h x o) a -
        Real.log (barrierHessian h x).det =
        (scaledLogDet (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) a -
          scaledLogDet (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) 0 -
          a * scaledLogDetFirst
            (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) 0) +
        (scaledLogDet (augmentedRows h x o (queryOffset h x o + a))
            (augmentedMotions h x o) 0 -
          Real.log (barrierHessian h x).det) +
        a * scaledLogDetFirst
          (augmentedRows h x o (queryOffset h x o + a))
          (augmentedMotions h x o) 0 := by ring
    _ ≤ rowCurvatureSum (augmentedMotions h x o) a -
        gammaPlus a motion.positiveEnergy +
        Real.log (1 + 1 / (queryOffset h x o + a) ^ 2) +
        a * (2 * electricalCubeMoment h x o /
          (1 + (queryOffset h x o + a) ^ 2)) := by
      rw [hzero, scaledLogDetFirst_augmented_zero hc o ht]
      rw [scaledLogDetFirst_augmented_zero hc o ht] at hcurveSave
      linarith
    _ = Real.log (1 + 1 / (queryOffset h x o + a) ^ 2) +
        ∑ i : OldRowIndex h,
          phiPlus (queryOffset h x o) a
            (electricalMotion h x o (indexedBarrierRow h i)) -
        gammaPlus a motion.positiveEnergy := by
      rw [augmented_rowCurvatureSum]
      unfold electricalCubeMoment phiPlus
      have hcubic :
          a * (2 * (∑ i : OldRowIndex h,
              electricalMotion h x o (indexedBarrierRow h i) ^ 3) /
                (1 + (queryOffset h x o + a) ^ 2)) =
            ∑ i : OldRowIndex h,
              (2 * a / (1 + (queryOffset h x o + a) ^ 2)) *
                electricalMotion h x o (indexedBarrierRow h i) ^ 3 := by
        calc
          _ = (2 * a / (1 + (queryOffset h x o + a) ^ 2)) *
              ∑ i : OldRowIndex h,
                electricalMotion h x o (indexedBarrierRow h i) ^ 3 := by ring
          _ = _ := by rw [Finset.mul_sum]
      rw [hcubic, Finset.sum_add_distrib]
      ring

/-- Equation (47), including the reflected `Γ₋` saving. -/
theorem negative_scaledLogDet_bound_strengthened {h : History n}
    {x : Placement n} (hc : IsVolumetricCenter h x) (o : Observation n)
    {delta b : ℝ} (hdelta : delta = queryOffset h x o)
    (hb0 : 0 < b) (hb1 : b < 1) (hcross : delta < b) :
    scaledLogDet (augmentedRows h x o (b - delta))
          (augmentedMotions h x o) (-b) -
        Real.log (barrierHessian h x).det ≤
      Real.log (1 + 1 / (b - delta) ^ 2) +
        ∑ i : OldRowIndex h,
          phiMinus delta b
            (electricalMotion h x o (indexedBarrierRow h i)) -
        gammaMinus b
          (electricalNormalizedMotions h x o hc.1).positiveEnergy := by
  subst delta
  have ht : b - queryOffset h x o ≠ 0 := ne_of_gt (sub_pos.2 hcross)
  let V := augmentedRows h x o (b - queryOffset h x o)
  let d := augmentedMotions h x o
  let motion := electricalNormalizedMotions h x o hc.1
  let reflected := motion.neg
  have hcurve := scaledLogDet_endpoint_sub_tangent_le_strengthened
    (V := V) (d := -d) hb0
    (fun s hs i => by
      rw [show rowDenominator (-d) s i = rowDenominator d (-s) i by
        simp [rowDenominator, d]]
      apply augmented_rowDenominator_ne hc.1 o
      rw [abs_neg, abs_of_nonneg hs.1]
      exact hs.2.trans_lt hb1)
    (fun s hs => by
      rw [scaledGram_neg]
      apply scaledGram_augmented_det_pos hc.1 o
      rw [abs_neg, abs_of_nonneg hs.1]
      exact hs.2.trans_lt hb1)
  have hintegral :
      (∫ s in (0 : ℝ)..b, (b - s) * scaledRateGap (-d) s ^ 2) =
        ∫ s in (0 : ℝ)..b, (b - s) *
          (reflected.positiveRateNorm s - reflected.negativeRateNorm s) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) b := by
      simpa [Set.uIcc_of_le hb0.le] using hs
    change (b - s) * scaledRateGap (-(augmentedMotions h x o)) s ^ 2 =
      (b - s) * (reflected.positiveRateNorm s - reflected.negativeRateNorm s) ^ 2
    rw [scaledRateGap_neg_augmented_eq o hc.1 hs'.1 (hs'.2.trans_lt hb1)]
  dsimp only [d] at hintegral
  rw [hintegral] at hcurve
  have hgamma := reflected.gammaPlus_le_integratedRateGap hb0.le hb1
  have hgammaMinus : gammaMinus b motion.positiveEnergy ≤
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..b, (b - s) *
        (reflected.positiveRateNorm s - reflected.negativeRateNorm s) ^ 2 := by
    have henergy : reflected.positiveEnergy = 1 - motion.positiveEnergy := by
      rw [show reflected = motion.neg by rfl, NormalizedMotions.positiveEnergy_neg,
        motion.negativeEnergy_eq]
    simpa [gammaMinus, henergy] using hgamma
  have hcurveSave :
      scaledLogDet V (-d) b - scaledLogDet V (-d) 0 -
          b * scaledLogDetFirst V (-d) 0 ≤
        rowCurvatureSum (-d) b - gammaMinus b motion.positiveEnergy := by
    linarith
  rw [scaledLogDet_neg] at hcurveSave
  rw [show scaledLogDet V (-d) 0 = scaledLogDet V d 0 by
    simpa using scaledLogDet_neg V d 0] at hcurveSave
  rw [scaledLogDetFirst_neg_zero V d] at hcurveSave
  have hcurve' :
      scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) (-b) -
          scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0 +
          b * scaledLogDetFirst
            (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0 ≤
        rowCurvatureSum (-(augmentedMotions h x o)) b -
          gammaMinus b motion.positiveEnergy := by
    dsimp only [V, d] at hcurveSave ⊢
    convert hcurveSave using 1 <;> ring
  have hfirst := scaledLogDetFirst_augmented_zero hc o ht
  have hzero := scaledLogDet_zero_sub_old hc.1 o ht
  calc
    scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
          (augmentedMotions h x o) (-b) -
        Real.log (barrierHessian h x).det =
        (scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) (-b) -
          scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0 +
          b * scaledLogDetFirst
            (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0) +
        (scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0 -
          Real.log (barrierHessian h x).det) -
        b * scaledLogDetFirst
          (augmentedRows h x o (b - queryOffset h x o))
          (augmentedMotions h x o) 0 := by ring
    _ ≤ rowCurvatureSum (-(augmentedMotions h x o)) b -
        gammaMinus b motion.positiveEnergy +
        Real.log (1 + 1 / (b - queryOffset h x o) ^ 2) -
        b * (2 * electricalCubeMoment h x o /
          (1 + (b - queryOffset h x o) ^ 2)) := by
      rw [hzero, hfirst]
      rw [hfirst] at hcurve'
      linarith
    _ = Real.log (1 + 1 / (b - queryOffset h x o) ^ 2) +
        ∑ i : OldRowIndex h,
          phiMinus (queryOffset h x o) b
            (electricalMotion h x o (indexedBarrierRow h i)) -
        gammaMinus b motion.positiveEnergy := by
      rw [rowCurvatureSum_neg_augmented]
      unfold electricalCubeMoment phiMinus
      have hcubic :
          -(b * (2 * (∑ i : OldRowIndex h,
              electricalMotion h x o (indexedBarrierRow h i) ^ 3) /
                (1 + (b - queryOffset h x o) ^ 2))) =
            ∑ i : OldRowIndex h,
              (-2 * b / (1 + (b - queryOffset h x o) ^ 2)) *
                electricalMotion h x o (indexedBarrierRow h i) ^ 3 := by
        calc
          _ = (-2 * b / (1 + (b - queryOffset h x o) ^ 2)) *
              ∑ i : OldRowIndex h,
                electricalMotion h x o (indexedBarrierRow h i) ^ 3 := by ring
          _ = _ := by rw [Finset.mul_sum]
      rw [sub_eq_add_neg, hcubic, Finset.sum_add_distrib]
      ring

end StrengthenedCurvature
end SortingAdversary
