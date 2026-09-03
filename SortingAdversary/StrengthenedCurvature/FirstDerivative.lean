import SortingAdversary.StrengthenedCurvature.IntegratedCurvature

/-!
# The first derivative at the old volumetric center

This file proves equation (35) of the strengthened-curvature note.  The proof
uses the exact Sherman--Morrison formula for the prospective comparison row
and the leverage-weighted stationarity equation of the old center.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {n : ℕ}

/-- The finite family of electrical row motions, with its unit-energy proof. -/
noncomputable def electricalNormalizedMotions (h : History n) (x : Placement n)
    (o : Observation n) (hx : InHistoryPolytope h x) :
    NormalizedMotions (OldRowIndex h) where
  alpha i := electricalMotion h x o (indexedBarrierRow h i)
  energy_one := by
    have henergy := electricalMotion_energy_one hx o
    have hlist : ((barrierRows h).map fun row =>
        electricalMotion h x o row ^ 2) =
      List.ofFn (fun i : OldRowIndex h =>
        electricalMotion h x o (indexedBarrierRow h i) ^ 2) := by
      calc
        (barrierRows h).map (fun row => electricalMotion h x o row ^ 2) =
            (List.ofFn (barrierRows h).get).map
              (fun row => electricalMotion h x o row ^ 2) := by
                rw [List.ofFn_get]
        _ = _ := (List.ofFn_comp' (barrierRows h).get
          (fun row => electricalMotion h x o row ^ 2)).symm
    rw [hlist] at henergy
    simpa [List.sum_ofFn] using henergy

/-- Cubic electrical moment `m₃`. -/
noncomputable def electricalCubeMoment (h : History n) (x : Placement n)
    (o : Observation n) : ℝ :=
  ∑ i : OldRowIndex h, electricalMotion h x o (indexedBarrierRow h i) ^ 3

private theorem normalizedOldRow_quadratic {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (i : OldRowIndex h) :
    normalizedOldRows h x i ⬝ᵥ
        Matrix.mulVec (barrierHessian h x)⁻¹ (normalizedOldRows h x i) =
      rowLeverage h x (indexedBarrierRow h i) := by
  let row := indexedBarrierRow h i
  have hs : row.slack x ≠ 0 :=
    ne_of_gt (barrierRows_slack_pos hx row (List.get_mem _ i))
  unfold normalizedOldRows rowLeverage
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← Finset.sum_mul]
  ring

private theorem normalizedOldRow_query_quadratic {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n)
    (i : OldRowIndex h) :
    normalizedOldRows h x i ⬝ᵥ
        Matrix.mulVec (barrierHessian h x)⁻¹
          (BarrierRow.ofObservation o).normal =
      Real.sqrt (effectiveResistance h x o) *
        electricalMotion h x o (indexedBarrierRow h i) := by
  let row := indexedBarrierRow h i
  have hs : row.slack x ≠ 0 :=
    ne_of_gt (barrierRows_slack_pos hx row (List.get_mem _ i))
  have hR : 0 < effectiveResistance h x o := effectiveResistance_pos hx o
  have hsqrt : Real.sqrt (effectiveResistance h x o) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hR)
  unfold normalizedOldRows electricalMotion normalizedRowMotion
  unfold electricalDirection BarrierRow.directionalSlack
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  field_simp [hs, hsqrt]

private theorem rowProjection_augmented_old_zero {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n)
    {t : ℝ} (ht : t ≠ 0) (i : OldRowIndex h) :
    rowProjection (scaledRows (augmentedRows h x o t)
      (augmentedMotions h x o) 0) (some i) (some i) =
      rowLeverage h x (indexedBarrierRow h i) -
        electricalMotion h x o (indexedBarrierRow h i) ^ 2 / (1 + t ^ 2) := by
  let rowVec : Placement n := normalizedOldRows h x i
  have hR : 0 < effectiveResistance h x o := effectiveResistance_pos hx o
  have hsqrt : 0 < Real.sqrt (effectiveResistance h x o) := Real.sqrt_pos.2 hR
  have hscale : Real.sqrt (effectiveResistance h x o) * t ≠ 0 :=
    mul_ne_zero hsqrt.ne' ht
  have hgram : scaledGram (augmentedRows h x o t)
      (augmentedMotions h x o) 0 =
      barrierHessian h x + scaledRankOne (BarrierRow.ofObservation o).normal
        (Real.sqrt (effectiveResistance h x o) * t) := by
    simpa [electricalLine] using scaledGram_augmented_eq hx o t (s := 0) (by norm_num)
  have hrow (v : Item n) :
      scaledRows (augmentedRows h x o t) (augmentedMotions h x o) 0
          (some i) v = rowVec v := by
    simpa [rowVec, electricalLine] using
      scaledRows_augmented_some hx o t 0 (by norm_num) i v
  have hprojection :
      rowProjection (scaledRows (augmentedRows h x o t)
        (augmentedMotions h x o) 0) (some i) (some i) =
        rowVec ⬝ᵥ Matrix.mulVec
          (barrierHessian h x + scaledRankOne
            (BarrierRow.ofObservation o).normal
            (Real.sqrt (effectiveResistance h x o) * t))⁻¹ rowVec := by
    simp only [rowProjection, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Matrix.mulVec]
    rw [show columnGram (scaledRows (augmentedRows h x o t)
        (augmentedMotions h x o) 0) =
      barrierHessian h x + scaledRankOne (BarrierRow.ofObservation o).normal
        (Real.sqrt (effectiveResistance h x o) * t) by
          simpa [scaledGram] using hgram]
    simp_rw [hrow]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hprojection]
  rw [quadratic_nonsingInv_add_scaledRankOne _ (barrierHessian_posDef hx)
    (BarrierRow.ofObservation o).normal rowVec
    (Real.sqrt (effectiveResistance h x o) * t) hscale]
  rw [normalizedOldRow_quadratic hx i,
    normalizedOldRow_query_quadratic hx o i]
  change _ = rowLeverage h x (indexedBarrierRow h i) - _
  congr 1
  rw [show (BarrierRow.ofObservation o).normal ⬝ᵥ
      Matrix.mulVec (barrierHessian h x)⁻¹
        (BarrierRow.ofObservation o).normal = effectiveResistance h x o by rfl]
  have hsquare : Real.sqrt (effectiveResistance h x o) ^ 2 =
      effectiveResistance h x o := Real.sq_sqrt hR.le
  field_simp [hR.ne', hsqrt.ne']
  nlinarith

/-- Equation (35): stationarity cancels the leverage-weighted linear term,
leaving only the cubic electrical moment. -/
theorem scaledLogDetFirst_augmented_zero {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (o : Observation n) {t : ℝ} (ht : t ≠ 0) :
    scaledLogDetFirst (augmentedRows h x o t) (augmentedMotions h x o) 0 =
      2 * electricalCubeMoment h x o / (1 + t ^ 2) := by
  rw [scaledLogDetFirst_eq_projectionDiagonal _ _ 0
    (augmented_rowDenominator_ne hc.1 o (by norm_num))]
  rw [Fintype.sum_option]
  simp only [scaledRate, augmentedMotions, rowDenominator, zero_mul, add_zero,
    zero_div, mul_zero, zero_add]
  simp_rw [rowProjection_augmented_old_zero hc.1 o ht]
  have hbalance := hc.electrical_balance o
  have hbalanceFin :
      ∑ i : OldRowIndex h,
        rowLeverage h x (indexedBarrierRow h i) *
          electricalMotion h x o (indexedBarrierRow h i) = 0 := by
    have hlist : ((barrierRows h).map fun row =>
        rowLeverage h x row * electricalMotion h x o row) =
      List.ofFn (fun i : OldRowIndex h =>
        rowLeverage h x (indexedBarrierRow h i) *
          electricalMotion h x o (indexedBarrierRow h i)) := by
      calc
        (barrierRows h).map (fun row =>
            rowLeverage h x row * electricalMotion h x o row) =
            (List.ofFn (barrierRows h).get).map (fun row =>
              rowLeverage h x row * electricalMotion h x o row) := by
                rw [List.ofFn_get]
        _ = _ := (List.ofFn_comp' (barrierRows h).get (fun row =>
          rowLeverage h x row * electricalMotion h x o row)).symm
    rw [hlist] at hbalance
    simpa [List.sum_ofFn] using hbalance
  simp only [div_one]
  rw [show (∑ i : OldRowIndex h,
      (rowLeverage h x (indexedBarrierRow h i) -
          electricalMotion h x o (indexedBarrierRow h i) ^ 2 / (1 + t ^ 2)) *
        electricalMotion h x o (indexedBarrierRow h i)) =
      -(electricalCubeMoment h x o) / (1 + t ^ 2) by
    unfold electricalCubeMoment
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, hbalanceFin, zero_sub]
    have hsum :
        (∑ i : OldRowIndex h,
          electricalMotion h x o (indexedBarrierRow h i) ^ 2 /
              (1 + t ^ 2) *
            electricalMotion h x o (indexedBarrierRow h i)) =
          (∑ i : OldRowIndex h,
          electricalMotion h x o (indexedBarrierRow h i) ^ 3) /
            (1 + t ^ 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring]
  simp [electricalCubeMoment]
  ring

end StrengthenedCurvature
end SortingAdversary
