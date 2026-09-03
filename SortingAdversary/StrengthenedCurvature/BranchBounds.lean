import SortingAdversary.StrengthenedCurvature.FirstDerivative

/-!
# Integrated bounds for the two deterministic trial branches

This file turns the matrix curvature theorem into equations (46) and (48) of
the strengthened note (and equations (32) and (33) of the earlier curvature
note).  The stronger sign saving can be subtracted later; the bounds here are
already sufficient for the fully efficient `7.361` certificate.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {n : ℕ}

private theorem scaledLogDet_zero_sub_old {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) {t : ℝ} (ht : t ≠ 0) :
    scaledLogDet (augmentedRows h x o t) (augmentedMotions h x o) 0 -
        Real.log (barrierHessian h x).det =
      Real.log (1 + 1 / t ^ 2) := by
  rw [scaledLogDet, scaledGram_augmented_det_zero hx o ht]
  have hdet : 0 < (barrierHessian h x).det := (barrierHessian_posDef hx).det_pos
  have hfactor : 0 < 1 + 1 / t ^ 2 := by positivity
  rw [Real.log_mul hdet.ne' hfactor.ne']
  ring

private theorem augmented_rowCurvatureSum {h : History n} {x : Placement n}
    (o : Observation n) (s : ℝ) :
    rowCurvatureSum (augmentedMotions h x o) s =
      ∑ i : OldRowIndex h,
        3 * (s * electricalMotion h x o (indexedBarrierRow h i) -
          Real.log (1 + s * electricalMotion h x o (indexedBarrierRow h i))) := by
  rw [rowCurvatureSum, Finset.sum_apply, Fintype.sum_option]
  simp [augmentedMotions, rowCurvaturePrimitive]

/-- Equation (46) without the optional strengthened-curvature saving. -/
theorem positive_scaledLogDet_bound {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (o : Observation n) {delta a : ℝ}
    (ho : 0 ≤ (BarrierRow.ofObservation o).slack x)
    (hdelta : delta = queryOffset h x o) (ha0 : 0 < a) (ha1 : a < 1) :
    scaledLogDet (augmentedRows h x o (delta + a))
          (augmentedMotions h x o) a -
        Real.log (barrierHessian h x).det ≤
      Real.log (1 + 1 / (delta + a) ^ 2) +
        ∑ i : OldRowIndex h,
          phiPlus delta a
            (electricalMotion h x o (indexedBarrierRow h i)) := by
  subst delta
  have ht : queryOffset h x o + a ≠ 0 := by
    exact ne_of_gt (add_pos_of_nonneg_of_pos (queryOffset_nonneg hc.1 ho) ha0)
  have hcurve := scaledLogDet_endpoint_sub_tangent_le
    (V := augmentedRows h x o (queryOffset h x o + a))
    (d := augmentedMotions h x o) ha0
    (fun s hs => augmented_rowDenominator_ne hc.1 o (by
      rw [abs_of_nonneg hs.1]
      exact hs.2.trans_lt ha1))
    (fun s hs => scaledGram_augmented_det_pos hc.1 o _ (by
      rw [abs_of_nonneg hs.1]
      exact hs.2.trans_lt ha1))
  rw [scaledLogDetFirst_augmented_zero hc o ht] at hcurve
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
    _ ≤ rowCurvatureSum (augmentedMotions h x o) a +
        Real.log (1 + 1 / (queryOffset h x o + a) ^ 2) +
        a * (2 * electricalCubeMoment h x o /
          (1 + (queryOffset h x o + a) ^ 2)) := by
      rw [hzero, scaledLogDetFirst_augmented_zero hc o ht]
      linarith
    _ = Real.log (1 + 1 / (queryOffset h x o + a) ^ 2) +
        ∑ i : OldRowIndex h,
          phiPlus (queryOffset h x o) a
            (electricalMotion h x o (indexedBarrierRow h i)) := by
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

section Reflection

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]
  [DecidableEq ρ] [DecidableEq κ]

private theorem scaledRows_neg (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    scaledRows V (-d) s = scaledRows V d (-s) := by
  ext i j
  simp only [scaledRows, Pi.neg_apply, rowDenominator]
  congr 1
  ring

private theorem scaledGram_neg (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    scaledGram V (-d) s = scaledGram V d (-s) := by
  simp only [scaledGram, scaledRows_neg]

private theorem scaledLogDet_neg (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    scaledLogDet V (-d) s = scaledLogDet V d (-s) := by
  simp only [scaledLogDet, scaledGram_neg]

private theorem scaledLogDetFirst_neg_zero
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) :
    scaledLogDetFirst V (-d) 0 = -scaledLogDetFirst V d 0 := by
  rw [scaledLogDetFirst_eq_projectionDiagonal V (-d) 0 (by
      intro i
      simp [rowDenominator]),
    scaledLogDetFirst_eq_projectionDiagonal V d 0 (by
      intro i
      simp [rowDenominator])]
  rw [scaledRows_neg]
  simp only [neg_zero, scaledRate, rowDenominator, Pi.neg_apply, zero_mul,
    add_zero, div_one]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

end Reflection

private theorem rowCurvatureSum_neg_augmented {h : History n}
    {x : Placement n} (o : Observation n) (b : ℝ) :
    rowCurvatureSum (-(augmentedMotions h x o)) b =
      ∑ i : OldRowIndex h,
        3 * (-b * electricalMotion h x o (indexedBarrierRow h i) -
          Real.log (1 - b * electricalMotion h x o (indexedBarrierRow h i))) := by
  rw [rowCurvatureSum, Finset.sum_apply, Fintype.sum_option]
  simp [augmentedMotions, rowCurvaturePrimitive]
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> ring

/-- Equation (48) without the optional strengthened-curvature saving. -/
theorem negative_scaledLogDet_bound {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (o : Observation n) {delta b : ℝ}
    (hdelta : delta = queryOffset h x o) (hb0 : 0 < b) (hb1 : b < 1)
    (hcross : delta < b) :
    scaledLogDet (augmentedRows h x o (b - delta))
          (augmentedMotions h x o) (-b) -
        Real.log (barrierHessian h x).det ≤
      Real.log (1 + 1 / (b - delta) ^ 2) +
        ∑ i : OldRowIndex h,
          phiMinus delta b
            (electricalMotion h x o (indexedBarrierRow h i)) := by
  subst delta
  have ht : b - queryOffset h x o ≠ 0 := ne_of_gt (sub_pos.2 hcross)
  let V := augmentedRows h x o (b - queryOffset h x o)
  let d := augmentedMotions h x o
  have hcurve := scaledLogDet_endpoint_sub_tangent_le
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
  rw [scaledLogDet_neg] at hcurve
  rw [show scaledLogDet V (-d) 0 = scaledLogDet V d 0 by
    simpa using scaledLogDet_neg V d 0] at hcurve
  rw [scaledLogDetFirst_neg_zero V d] at hcurve
  have hfirst := scaledLogDetFirst_augmented_zero hc o ht
  have hzero := scaledLogDet_zero_sub_old hc.1 o ht
  dsimp only [V, d] at hcurve
  have hcurve' :
      scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) (-b) -
          scaledLogDet (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0 +
          b * scaledLogDetFirst
            (augmentedRows h x o (b - queryOffset h x o))
            (augmentedMotions h x o) 0 ≤
        rowCurvatureSum (-(augmentedMotions h x o)) b := by
    linarith [hcurve]
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
    _ ≤ rowCurvatureSum (-(augmentedMotions h x o)) b +
        Real.log (1 + 1 / (b - queryOffset h x o) ^ 2) -
        b * (2 * electricalCubeMoment h x o /
          (1 + (b - queryOffset h x o) ^ 2)) := by
      rw [hzero, hfirst]
      rw [hfirst] at hcurve'
      linarith [hcurve']
    _ = Real.log (1 + 1 / (b - queryOffset h x o) ^ 2) +
        ∑ i : OldRowIndex h,
          phiMinus (queryOffset h x o) b
            (electricalMotion h x o (indexedBarrierRow h i)) := by
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
