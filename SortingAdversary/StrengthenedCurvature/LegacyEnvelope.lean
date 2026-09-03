import SortingAdversary.StrengthenedCurvature.BranchBounds

/-!
# The one-dimensional curvature envelope

This is the deterministic schedule from the curvature-volumetric notes.  It
uses no sign-energy state and no majority/counting oracle.  The schedule is a
function only of the normalized query offset `delta`.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

/-- The fixed centered displacement `1 / √3`. -/
noncomputable def legacyRadius : ℝ := Real.sqrt (1 / 3)

noncomputable def legacyTPlus (delta : ℝ) : ℝ :=
  legacyRadius + (4 / 5 : ℝ) * delta

noncomputable def legacyTMinus (delta : ℝ) : ℝ :=
  legacyRadius - (4 / 5 : ℝ) * delta

noncomputable def legacyA (delta : ℝ) : ℝ :=
  legacyRadius - (1 / 5 : ℝ) * delta

noncomputable def legacyB (delta : ℝ) : ℝ :=
  legacyRadius + (1 / 5 : ℝ) * delta

noncomputable def legacyA0 (delta : ℝ) : ℝ :=
  legacyA delta / (1 + legacyTPlus delta ^ 2)

noncomputable def legacyB0 (delta : ℝ) : ℝ :=
  legacyB delta / (1 + legacyTMinus delta ^ 2)

/-- The proof-only convex-combination witness which cancels the cubic
electrical moment.  It is not computed by the adversary. -/
noncomputable def legacyLambda (delta : ℝ) : ℝ :=
  legacyB0 delta / (legacyA0 delta + legacyB0 delta)

/-- The one-dimensional scalar envelope checked by directed intervals. -/
noncomputable def legacyEnvelope (delta : ℝ) : ℝ :=
  let a := legacyA delta
  let b := legacyB delta
  let lambda := legacyLambda delta
  lambda * Real.log (1 + 1 / legacyTPlus delta ^ 2) +
    (1 - lambda) * Real.log (1 + 1 / legacyTMinus delta ^ 2) +
    max (rho delta a b lambda (-1)) (rho delta a b lambda 1)

theorem legacyRadius_pos : 0 < legacyRadius := by
  rw [legacyRadius, Real.sqrt_pos]
  norm_num

theorem half_lt_legacyRadius : (1 / 2 : ℝ) < legacyRadius := by
  rw [legacyRadius, Real.lt_sqrt (by norm_num)]
  norm_num

theorem legacyRadius_lt_three_fifths : legacyRadius < (3 / 5 : ℝ) := by
  rw [legacyRadius, Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

section Feasibility

variable {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ (397 / 1000 : ℝ))

include hd0 hd1

theorem legacyTPlus_pos : 0 < legacyTPlus delta := by
  unfold legacyTPlus
  nlinarith [legacyRadius_pos]

theorem legacyTMinus_pos : 0 < legacyTMinus delta := by
  unfold legacyTMinus
  nlinarith [half_lt_legacyRadius]

theorem legacyA_pos : 0 < legacyA delta := by
  unfold legacyA
  nlinarith [half_lt_legacyRadius]

theorem legacyA_lt_one : legacyA delta < 1 := by
  unfold legacyA
  nlinarith [legacyRadius_lt_three_fifths]

theorem legacyB_pos : 0 < legacyB delta := by
  unfold legacyB
  nlinarith [legacyRadius_pos]

theorem legacyB_lt_one : legacyB delta < 1 := by
  unfold legacyB
  nlinarith [legacyRadius_lt_three_fifths]

theorem delta_lt_legacyB : delta < legacyB delta := by
  unfold legacyB
  nlinarith [half_lt_legacyRadius]

theorem legacyA0_pos : 0 < legacyA0 delta := by
  exact div_pos (legacyA_pos hd0 hd1) (by positivity)

theorem legacyB0_pos : 0 < legacyB0 delta := by
  exact div_pos (legacyB_pos hd0 hd1) (by positivity)

theorem legacyLambda_pos : 0 < legacyLambda delta := by
  exact div_pos (legacyB0_pos hd0 hd1)
    (add_pos (legacyA0_pos hd0 hd1) (legacyB0_pos hd0 hd1))

theorem legacyLambda_lt_one : legacyLambda delta < 1 := by
  rw [legacyLambda, div_lt_one
    (add_pos (legacyA0_pos hd0 hd1) (legacyB0_pos hd0 hd1))]
  exact lt_add_of_pos_left _ (legacyA0_pos hd0 hd1)

end Feasibility

/-- The matrix analysis and endpoint convexity reduce both deterministic
trial branches to the one-dimensional envelope. -/
theorem min_trial_scaledLogDet_le_legacyEnvelope
    {n : ℕ} {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (q : Query n)
    {delta : ℝ} (hdelta : delta = queryOffset h x (centerOrientation x q))
    (hd1 : delta ≤ (397 / 1000 : ℝ)) :
    let o := centerOrientation x q
    min
      (scaledLogDet (augmentedRows h x o (legacyTPlus delta))
          (augmentedMotions h x o) (legacyA delta) -
        Real.log (barrierHessian h x).det)
      (scaledLogDet (augmentedRows h x o (legacyTMinus delta))
          (augmentedMotions h x o) (-legacyB delta) -
        Real.log (barrierHessian h x).det) ≤
      legacyEnvelope delta := by
  dsimp only
  let o := centerOrientation x q
  have hd0 : 0 ≤ delta := by
    subst delta
    exact queryOffset_nonneg hc.1 (centerOrientation_slack_nonneg x q)
  have htpa : delta + legacyA delta = legacyTPlus delta := by
    simp only [legacyA, legacyTPlus]
    ring
  have htmb : legacyB delta - delta = legacyTMinus delta := by
    simp only [legacyB, legacyTMinus]
    ring
  have hplus := positive_scaledLogDet_bound hc o
    (centerOrientation_slack_nonneg x q) hdelta
    (legacyA_pos hd0 hd1) (legacyA_lt_one hd0 hd1)
  rw [htpa] at hplus
  have hminus := negative_scaledLogDet_bound hc o hdelta
    (legacyB_pos hd0 hd1) (legacyB_lt_one hd0 hd1)
    (delta_lt_legacyB hd0 hd1)
  rw [htmb] at hminus
  let motion := electricalNormalizedMotions h x o hc.1
  let lambda := legacyLambda delta
  have hl0 : 0 ≤ lambda := (legacyLambda_pos hd0 hd1).le
  have hl1 : lambda ≤ 1 := (legacyLambda_lt_one hd0 hd1).le
  have hframe := normalizedMotions_unit_endpoint_reduction motion delta
    (legacyA delta) (legacyB delta) lambda
    (legacyA_pos hd0 hd1).le (legacyA_lt_one hd0 hd1)
    (legacyB_pos hd0 hd1).le (legacyB_lt_one hd0 hd1) hl0 hl1
  have hweighted := min_le_weighted_average (x :=
      Real.log (1 + 1 / legacyTPlus delta ^ 2) +
        ∑ i : OldRowIndex h,
          phiPlus delta (legacyA delta)
            (electricalMotion h x o (indexedBarrierRow h i))) (y :=
      Real.log (1 + 1 / legacyTMinus delta ^ 2) +
        ∑ i : OldRowIndex h,
          phiMinus delta (legacyB delta)
            (electricalMotion h x o (indexedBarrierRow h i))) hl0 hl1
  calc
    min
      (scaledLogDet (augmentedRows h x o (legacyTPlus delta))
          (augmentedMotions h x o) (legacyA delta) -
        Real.log (barrierHessian h x).det)
      (scaledLogDet (augmentedRows h x o (legacyTMinus delta))
          (augmentedMotions h x o) (-legacyB delta) -
        Real.log (barrierHessian h x).det) ≤
        min
          (Real.log (1 + 1 / legacyTPlus delta ^ 2) +
            ∑ i : OldRowIndex h,
              phiPlus delta (legacyA delta)
                (electricalMotion h x o (indexedBarrierRow h i)))
          (Real.log (1 + 1 / legacyTMinus delta ^ 2) +
            ∑ i : OldRowIndex h,
              phiMinus delta (legacyB delta)
                (electricalMotion h x o (indexedBarrierRow h i))) :=
      min_le_min hplus hminus
    _ ≤ lambda *
          (Real.log (1 + 1 / legacyTPlus delta ^ 2) +
            ∑ i : OldRowIndex h,
              phiPlus delta (legacyA delta)
                (electricalMotion h x o (indexedBarrierRow h i))) +
        (1 - lambda) *
          (Real.log (1 + 1 / legacyTMinus delta ^ 2) +
            ∑ i : OldRowIndex h,
              phiMinus delta (legacyB delta)
                (electricalMotion h x o (indexedBarrierRow h i))) := hweighted
    _ = lambda * Real.log (1 + 1 / legacyTPlus delta ^ 2) +
          (1 - lambda) * Real.log (1 + 1 / legacyTMinus delta ^ 2) +
          ∑ i : OldRowIndex h,
            phiAverage delta (legacyA delta) (legacyB delta) lambda
              (electricalMotion h x o (indexedBarrierRow h i)) := by
      simp only [phiAverage]
      rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_add_distrib]
      ring
    _ ≤ lambda * Real.log (1 + 1 / legacyTPlus delta ^ 2) +
          (1 - lambda) * Real.log (1 + 1 / legacyTMinus delta ^ 2) +
          max (rho delta (legacyA delta) (legacyB delta) lambda (-1))
            (rho delta (legacyA delta) (legacyB delta) lambda 1) := by
      dsimp only [motion, electricalNormalizedMotions] at hframe
      let base := lambda * Real.log (1 + 1 / legacyTPlus delta ^ 2) +
        (1 - lambda) * Real.log (1 + 1 / legacyTMinus delta ^ 2)
      calc
        base + ∑ i : OldRowIndex h,
            phiAverage delta (legacyA delta) (legacyB delta) lambda
              (electricalMotion h x o (indexedBarrierRow h i)) =
            (∑ i : OldRowIndex h,
              phiAverage delta (legacyA delta) (legacyB delta) lambda
                (electricalMotion h x o (indexedBarrierRow h i))) + base :=
          add_comm _ _
        _ ≤ max (rho delta (legacyA delta) (legacyB delta) lambda (-1))
              (rho delta (legacyA delta) (legacyB delta) lambda 1) + base :=
          add_le_add_left hframe base
        _ = base + max (rho delta (legacyA delta) (legacyB delta) lambda (-1))
              (rho delta (legacyA delta) (legacyB delta) lambda 1) :=
          add_comm _ _
    _ = legacyEnvelope delta := by rfl

end StrengthenedCurvature
end SortingAdversary
