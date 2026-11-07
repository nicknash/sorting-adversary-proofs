import SortingAdversary.Optimal.MeasuredOracleBudget
import SortingAdversary.Optimal.LocalOracleWork

/-!
# Actual stage caps and binary operand envelopes for the measured oracles

The graph-size premises are discharged from the maintained degree bound and
the stage's computed radius allowance. The same outer budget `2*n` controls
all exact local count integers, normalized rational fields, and the cross
products used to compare the two stopping estimates. No local counting
algorithm or runtime value is replaced in this module.
-/

namespace SortingAdversary.Optimal.MeasuredOracleBounds

open PrimitiveWork MeasuredLocalOracle WeakMaps LocalChoice GraphBalls BallSchedule
open RepresentationWork WidthRepair MeasuredOracleBudget

variable {n K : ℕ} {s : State n}

theorem comparison_ball_logCap (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R ε : ℚ) (x y : Fin n) (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε)
    (hc : LocalOracleWork.comparisonBallBound H d R ε ≤ Parameters.logCap n) :
    (twoBalls s.rows.active x y radius).card ≤ Parameters.logCap n := by
  rw [hr]
  exact (LocalAccuracy.queryBall_card s.rows.view H d R ε g.degree x y).trans hc

theorem cdf_ball_logCap (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R ε : ℚ) (x : Fin n) (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R ε)
    (hc : LocalOracleWork.cdfBallBound H d R ε ≤ Parameters.logCap n) :
    (ball s.rows.active x radius).card ≤ Parameters.logCap n := by
  rw [hr]
  exact (CDFAccuracy.queryBall_card s.rows.view H d R ε g.degree x).trans hc

theorem ordinary_work_of_radius_logCap (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : SeparatedPins.HasMate s.pool v)
    (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R (1 / 16))
    (c : ℕ) (hn : n ≠ 0)
    (hc : LocalOracleWork.cdfBallBound H d R (1 / 16) ≤ Parameters.logCap n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (MeasuredOrdinaryPromotion.atRadius a H d g R hR v hmark hv hm radius hr).work ≤
      MeasuredOrdinaryPromotion.workBound n s.pool.palette A
        (MeasuredOracleBudget.cdfPolynomial n (2 * n) c A) + 1 :=
  ordinary_work_logCap a hA H d g R hR v hmark hv hm radius hr c hn
    (cdf_ball_logCap H d g R (1 / 16) v radius hr hc) hK

theorem stopping_work_of_radius_logCap (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (p : RecursiveController.Parameters)
    (ready : PassiveLocalState.Ready p.repair.scale p.repair.D p.repair.H s.pool ⟨s.rows, s.order⟩)
    (x y : Fin n) (hxy : s.pool.system.edge x y ≠ true) (hyx : s.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ colour, s.pool.pins x = some colour ∧ s.pool.pins y = some colour)
    (radius : ℕ)
    (hr : radius = p.repair.scale.H * LocalParameters.sweepCount p.repair.scale.H
      (LocalAccuracy.influenceSize p.repair.scale.H p.repair.d) p.repair.scale.R p.error)
    (c : ℕ) (hn : n ≠ 0)
    (hc : LocalOracleWork.comparisonBallBound p.repair.scale.H p.repair.d
      p.repair.scale.R p.error ≤ Parameters.logCap n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (MeasuredStopping.atRadius a p ready x y hxy hyx hstop radius hr).work ≤
      StoppingTestsWork.workBound n A +
        2 * MeasuredOracleBudget.branchPolynomial n (2 * n) c A + 15 :=
  stopping_work_logCap a hA p ready x y hxy hyx hstop radius hr c hn
    (comparison_ball_logCap p.repair.scale.H p.repair.d
      (NormalizedBounds.readyBounds ready _ _ p.height_old p.degree_old)
      p.repair.scale.R p.error x y radius hr hc) hK

/-- The two reduced rational fields are bounded by the exact integers fed
to the measured normalization routine, even at a zero denominator. -/
theorem branch_sizes (a : LocalAccess s) (r : ℕ) (x y : Fin n) (N c : ℕ)
    (hn : n ≤ N) (hK : s.pool.palette + 1 ≤ c * N) :
    Nat.size (branch a r x y).value.num.natAbs ≤ bitBound N c ∧
      Nat.size (branch a r x y).value.den ≤ bitBound N c + 1 := by
  have hs := MeasuredOracleBudget.branchCounts_sizes (prepare a).value r x y N c hn hK
  exact ⟨(RationalWork.ratio_num_size _ _).trans hs.1,
    (RationalWork.ratio_den_size _ _).trans (Nat.add_le_add_right hs.2 1)⟩

theorem cdf_sizes (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut N c : ℕ)
    (hn : n ≤ N) (hK : s.pool.palette + 1 ≤ c * N) :
    Nat.size (cdf a r x cut).value.num.natAbs ≤ bitBound N c ∧
      Nat.size (cdf a r x cut).value.den ≤ bitBound N c + 1 := by
  have hs := MeasuredOracleBudget.cdfCounts_sizes (prepare a).value r x cut N c hn hK
  exact ⟨(RationalWork.ratio_num_size _ _).trans hs.1,
    (RationalWork.ratio_den_size _ _).trans (Nat.add_le_add_right hs.2 1)⟩

/-- A common arithmetic polynomial for local numerator and denominator
widths. It is deliberately valid without a ball-size assumption. -/
def countBits (n c : ℕ) : ℕ := 2 * n * (c * (2 * n) + 2) + 2

theorem bitBound_double_le (n c : ℕ) : bitBound (2 * n) c + 1 ≤ countBits n c := by
  have h := bitBound_polynomial (2 * n) c
  unfold countBits
  omega

theorem branch_sizes_polynomial (a : LocalAccess s) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size (branch a r x y).value.num.natAbs ≤ countBits n c ∧
      Nat.size (branch a r x y).value.den ≤ countBits n c := by
  have hs := branch_sizes a r x y (2 * n) c (by omega)
    (hK.trans (Nat.mul_le_mul_left c (by omega : n ≤ 2 * n)))
  have hb := bitBound_double_le n c
  omega

theorem cdf_sizes_polynomial (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size (cdf a r x cut).value.num.natAbs ≤ countBits n c ∧
      Nat.size (cdf a r x cut).value.den ≤ countBits n c := by
  have hs := cdf_sizes a r x cut (2 * n) c (by omega)
    (hK.trans (Nat.mul_le_mul_left c (by omega : n ≤ 2 * n)))
  have hb := bitBound_double_le n c
  omega

/-- These are the actual signed multiplication outputs inspected by
`CalibrationWork.lessEqual`, which is also the stopping comparator. -/
theorem cross_product_sizes (left right : ℚ) (L R : ℕ)
    (hl : Nat.size left.num.natAbs ≤ L ∧ Nat.size left.den ≤ L)
    (hr : Nat.size right.num.natAbs ≤ R ∧ Nat.size right.den ≤ R) :
    Nat.size (left.num * (right.den : ℤ)).natAbs ≤ L + R ∧
      Nat.size (right.num * (left.den : ℤ)).natAbs ≤ L + R := by
  have hf := RationalWork.size_int_mul_le left.num (right.den : ℤ)
  have hb := RationalWork.size_int_mul_le right.num (left.den : ℤ)
  simp only [Int.natAbs_natCast] at hf hb
  omega

theorem stopping_cross_product_sizes (a : LocalAccess s) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size ((branch a r y x).value.num * ((branch a r x y).value.den : ℤ)).natAbs ≤
        2 * countBits n c ∧
      Nat.size ((branch a r x y).value.num * ((branch a r y x).value.den : ℤ)).natAbs ≤
        2 * countBits n c := by
  simpa only [two_mul] using cross_product_sizes _ _ (countBits n c) (countBits n c)
    (branch_sizes_polynomial a r y x c hK) (branch_sizes_polynomial a r x y c hK)

end SortingAdversary.Optimal.MeasuredOracleBounds
