import SortingAdversary.StrengthenedCurvature.LegacyCertificate
import SortingAdversary.StrengthenedCurvature.GeometricRule
import SortingAdversary.StrengthenedCurvature.CenterExistence

/-!
# The efficient deterministic one-comparison rule

For an informative query, orient the comparison toward the side containing
the current volumetric center.  At large normalized offset retain that side.
At small offset evaluate the two explicit electrical trial points and retain
the child with smaller volumetric potential.  This is exactly the algorithmic
adversary in the curvature-volumetric notes; scalar schedule witnesses are
used only in its proof.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- Per-informative-comparison potential budget for `K = 7.361`. -/
noncomputable def legacyComparisonBudget : ℝ :=
  Real.log (legacyK : ℝ) / (2 * Real.log 2)

theorem legacyComparisonBudget_nonneg : 0 ≤ legacyComparisonBudget := by
  exact div_nonneg (Real.log_nonneg (by norm_num [legacyK]))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))

private theorem historyPotential_child_le_of_logDet
    {n : ℕ} {h : History n} {x y : Placement n} (hc : IsVolumetricCenter h x)
    (o : Observation n) (hy : InHistoryPolytope (o :: h) y)
    (hlog : Real.log (barrierHessian (o :: h) y).det -
        Real.log (barrierHessian h x).det ≤ Real.log (legacyK : ℝ)) :
    historyPotential (o :: h) - historyPotential h ≤ legacyComparisonBudget := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    historyPotential (o :: h) - historyPotential h ≤
        volumetricValue₂ (o :: h) y - historyPotential h :=
      sub_le_sub_right (historyPotential_le_value hy) _
    _ = (Real.log (barrierHessian (o :: h) y).det -
          Real.log (barrierHessian h x).det) / (2 * Real.log 2) := by
      rw [hc.historyPotential_eq]
      simp only [volumetricValue₂, volumetricValue]
      field_simp [hlogtwo.ne']
    _ ≤ Real.log (legacyK : ℝ) / (2 * Real.log 2) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hlogtwo)).2 hlog
    _ = legacyComparisonBudget := rfl

private theorem center_answerHistory (h : History n) (x : Placement n)
    (q : Query n) :
    answerHistory h q (centerOrientation x q).answer =
      centerOrientation x q :: h := by
  generalize ho : centerOrientation x q = o
  unfold answerHistory
  cases o with
  | mk q' a =>
      have hq : q' = q := by
        have := congrArg Observation.query ho
        simpa using this.symm
      subst q'
      rfl

private theorem opposite_answerHistory (h : History n) (x : Placement n)
    (q : Query n) :
    answerHistory h q (oppositeObservation (centerOrientation x q)).answer =
      oppositeObservation (centerOrientation x q) :: h := by
  generalize ho : oppositeObservation (centerOrientation x q) = o
  unfold answerHistory
  cases o with
  | mk q' a =>
      have hq : q' = q := by
        have := congrArg Observation.query ho
        simpa using this.symm
      subst q'
      rfl

private theorem near_center_step {n : ℕ} {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (q : Query n)
    (hsmall : queryOffset h x (centerOrientation x q) ≤ (397 / 1000 : ℝ)) :
    ∃ a : Answer, Feasible (answerHistory h q a) ∧
      historyPotential (answerHistory h q a) - historyPotential h ≤
        legacyComparisonBudget := by
  let o := centerOrientation x q
  let delta := queryOffset h x o
  have hd0 : 0 ≤ delta := queryOffset_nonneg hc.1
    (centerOrientation_slack_nonneg x q)
  have htrials := min_trial_scaledLogDet_le_legacyEnvelope hc q
    (delta := delta) rfl hsmall
  have hcert := legacy_scalar_certificate hd0 hsmall
  have hmin :
      min
        (scaledLogDet (augmentedRows h x o (legacyTPlus delta))
            (augmentedMotions h x o) (legacyA delta) -
          Real.log (barrierHessian h x).det)
        (scaledLogDet (augmentedRows h x o (legacyTMinus delta))
            (augmentedMotions h x o) (-legacyB delta) -
          Real.log (barrierHessian h x).det) <
        Real.log (legacyK : ℝ) := htrials.trans_lt hcert
  let plusValue := scaledLogDet (augmentedRows h x o (legacyTPlus delta))
    (augmentedMotions h x o) (legacyA delta) -
      Real.log (barrierHessian h x).det
  let minusValue := scaledLogDet (augmentedRows h x o (legacyTMinus delta))
    (augmentedMotions h x o) (-legacyB delta) -
      Real.log (barrierHessian h x).det
  by_cases hpm : plusValue ≤ minusValue
  · have hplus : plusValue ≤ Real.log (legacyK : ℝ) := by
      rw [min_eq_left hpm] at hmin
      exact hmin.le
    refine ⟨o.answer, ?_, ?_⟩
    · rw [center_answerHistory]
      exact positiveTrial_feasible hc.1 o (centerOrientation_slack_nonneg x q)
        (legacyA_pos hd0 hsmall) (legacyA_lt_one hd0 hsmall)
    · rw [center_answerHistory]
      apply historyPotential_child_le_of_logDet hc o
        (positiveTrial_mem hc.1 o (centerOrientation_slack_nonneg x q)
          (legacyA_pos hd0 hsmall) (legacyA_lt_one hd0 hsmall))
      rw [← scaledGram_positiveTrial hc.1 o
        (legacyA_pos hd0 hsmall) (legacyA_lt_one hd0 hsmall)]
      dsimp only [plusValue] at hplus
      rw [show legacyTPlus delta = delta + legacyA delta by
        simp [legacyTPlus, legacyA]
        ring] at hplus
      simpa [scaledLogDet] using hplus
  · have hminusOrder : minusValue ≤ plusValue := le_of_not_ge hpm
    have hminus : minusValue ≤ Real.log (legacyK : ℝ) := by
      rw [min_eq_right hminusOrder] at hmin
      exact hmin.le
    refine ⟨(oppositeObservation o).answer, ?_, ?_⟩
    · rw [opposite_answerHistory]
      exact negativeTrial_feasible hc.1 o
        (legacyB_pos hd0 hsmall) (legacyB_lt_one hd0 hsmall)
        (delta_lt_legacyB hd0 hsmall)
    · rw [opposite_answerHistory]
      apply historyPotential_child_le_of_logDet hc (oppositeObservation o)
        (negativeTrial_mem hc.1 o
          (legacyB_pos hd0 hsmall) (legacyB_lt_one hd0 hsmall)
          (delta_lt_legacyB hd0 hsmall))
      rw [← scaledGram_negativeTrial hc.1 o
        (legacyB_pos hd0 hsmall) (legacyB_lt_one hd0 hsmall)]
      dsimp only [minusValue] at hminus
      rw [show legacyTMinus delta = legacyB delta - delta by
        simp [legacyTMinus, legacyB]
        ring] at hminus
      simpa [scaledLogDet] using hminus

private theorem large_offset_quotient {n : ℕ} {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (q : Query n)
    (hlarge : (397 / 1000 : ℝ) <
      queryOffset h x (centerOrientation x q)) :
    effectiveResistance h x (centerOrientation x q) /
        (BarrierRow.ofObservation (centerOrientation x q)).slack x ^ 2 ≤
      (legacyK : ℝ) - 1 := by
  let o := centerOrientation x q
  let delta := queryOffset h x o
  have hR := effectiveResistance_pos hx o
  have hsqrt := Real.sqrt_pos.2 hR
  have hdelta : 0 < delta := (by norm_num : (0 : ℝ) < 397 / 1000).trans hlarge
  have hratio : effectiveResistance h x o /
        (BarrierRow.ofObservation o).slack x ^ 2 = 1 / delta ^ 2 := by
    dsimp only [delta]
    rw [query_slack_eq_sqrt_mul_offset hx o]
    field_simp [hsqrt.ne', hdelta.ne']
    rw [Real.sq_sqrt hR.le]
  rw [hratio]
  have hsq : (397 / 1000 : ℝ) ^ 2 ≤ delta ^ 2 := by nlinarith
  have hinv : 1 / delta ^ 2 ≤ 1 / (397 / 1000 : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  calc
    1 / delta ^ 2 ≤ 1 / (397 / 1000 : ℝ) ^ 2 := hinv
    _ ≤ (legacyK : ℝ) - 1 := by norm_num [legacyK]

private theorem large_center_step {n : ℕ} {h : History n} {x : Placement n}
    (hc : IsVolumetricCenter h x) (q : Query n)
    (hlarge : (397 / 1000 : ℝ) <
      queryOffset h x (centerOrientation x q)) :
    ∃ a : Answer, Feasible (answerHistory h q a) ∧
      historyPotential (answerHistory h q a) - historyPotential h ≤
        legacyComparisonBudget := by
  let o := centerOrientation x q
  have hslack : 0 < (BarrierRow.ofObservation o).slack x := by
    rw [query_slack_eq_sqrt_mul_offset hc.1 o]
    exact mul_pos (Real.sqrt_pos.2 (effectiveResistance_pos hc.1 o))
      ((by norm_num : (0 : ℝ) < 397 / 1000).trans hlarge)
  have hxchild : InHistoryPolytope (o :: h) x := by
    refine ⟨hc.1.1, ?_⟩
    simpa using And.intro
      ((BarrierRow.realizesPlacement_iff_slack_pos o x).2 hslack) hc.1.2
  refine ⟨o.answer, ?_, ?_⟩
  · rw [center_answerHistory]
    exact feasible_of_mem_historyPolytope hxchild
  · rw [center_answerHistory]
    calc
      historyPotential (o :: h) - historyPotential h ≤
          volumetricValue₂ (o :: h) x - volumetricValue₂ h x := by
        rw [hc.historyPotential_eq]
        exact sub_le_sub_right (historyPotential_le_value hxchild) _
      _ ≤ legacyComparisonBudget := by
        exact volumetricValue₂_cons_sub_le hc.1 o hslack
          (by norm_num [legacyK]) (large_offset_quotient hc.1 q hlarge)

/-- The local rule from the notes, with all informative transitions proved. -/
noncomputable def efficientInformativeRule (n : ℕ) : InformativePotentialRule n where
  potential := historyPotential
  maxIncrease := legacyComparisonBudget
  maxIncrease_nonneg := legacyComparisonBudget_nonneg
  informativeStep := by
    intro h q hh _ _
    obtain ⟨x, hc⟩ := exists_volumetricCenter h hh
    by_cases hsmall : queryOffset h x (centerOrientation x q) ≤ (397 / 1000 : ℝ)
    · exact near_center_step hc q hsmall
    · exact large_center_step hc q (lt_of_not_ge hsmall)

/-- Total deterministic history-dependent potential rule, including repeated
and already implied comparisons. -/
noncomputable def efficientPotentialRule (n : ℕ) : PotentialRule n :=
  (efficientInformativeRule n).toPotentialRule

end StrengthenedCurvature
end SortingAdversary
