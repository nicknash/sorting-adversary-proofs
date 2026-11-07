import SortingAdversary.Optimal.MeasuredOrdinaryPromotion
import SortingAdversary.Optimal.MeasuredStopping
import SortingAdversary.Optimal.Parameters

/-!
# Counted oracle budgets at the actual uniform logarithmic cap

The stage accepts balls of size at most `log₂(n+1)`. All subset-DP bounds are
therefore instantiated with the honest outer budget `2*n`, which handles
sizes `n = 2^k-1` as well. The executed algorithms are unchanged. This module
also bounds their actual count and rational operand widths.
-/

namespace SortingAdversary.Optimal.MeasuredOracleBudget

open PrimitiveWork MeasuredLocalOracle WeakMaps LocalChoice GraphBalls BallSchedule
open RepresentationWork WidthRepair

variable {n K : ℕ} {s : State n}

theorem countLabels_work (data : LocalDPWork.Input n K) (C : ℕ) (cost : data.Cost C)
    (xs : List (Fin n)) (N c : ℕ) (hN : N ≠ 0)
    (hb : xs.length ≤ Nat.log 2 N) (hK : K ≤ c * N) :
    (countLabels data xs).work ≤ oneCountBound N c C := by
  have hc := cost_mono data cost (Nat.le_add_right C 5)
  exact LocalListDPWork.count_polynomial xs data.edge data.lower data.upper N c (C + 5)
    hN hb hK hc.1 hc.2.1 hc.2.2

theorem branchCounts_work (data : LocalDPWork.Input n K) (C : ℕ) (cost : data.Cost C)
    (r : ℕ) (x y : Fin n) (N c : ℕ) (hN : N ≠ 0)
    (hb : (twoBalls data.system.edge x y r).card ≤ Nat.log 2 N) (hK : K ≤ c * N) :
    (branchCounts data r x y).work ≤ labelsBound n C + 2 * oneCountBound N c (C + 4) + 3 := by
  have hlen : (labels data r x y).value.length ≤ Nat.log 2 N := by rw [labels_length]; exact hb
  have hl := labels_work data C cost r x y
  have hnum := countLabels_work (addRow data x y) (C + 4) (addRow_cost data C cost x y)
    (labels data r x y).value N c hN hlen hK
  have hden := countLabels_work data (C + 4) (cost_mono data cost (Nat.le_add_right C 4))
    (labels data r x y).value N c hN hlen hK
  change _ + _ + _ + 3 ≤ _
  omega

theorem cdfNumerator_work (data : LocalDPWork.Input n (K + 1)) (C : ℕ) (cost : data.Cost C)
    (xs : List (Fin n)) (x : Fin n) (cut N c : ℕ) (hN : N ≠ 0)
    (hb : xs.length ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    (cdfNumerator data xs x cut).work ≤ oneCountBound N c (C + 5) + 1 := by
  cases cut with
  | zero => exact Nat.le_add_left 1 _
  | succ cut =>
    exact Nat.add_le_add_right (countLabels_work (ceiling data x cut) (C + 5)
      (ceiling_cost data C cost x cut) xs N c hN hb hK) 1

theorem cdfCounts_work (data : LocalDPWork.Input n (K + 1)) (C : ℕ) (cost : data.Cost C)
    (r : ℕ) (x : Fin n) (cut N c : ℕ) (hN : N ≠ 0)
    (hb : (ball data.system.edge x r).card ≤ Nat.log 2 N) (hK : K + 1 ≤ c * N) :
    (cdfCounts data r x cut).work ≤ labelsBound n C + 2 * oneCountBound N c (C + 5) + 4 := by
  have hlen : (labels data r x x).value.length ≤ Nat.log 2 N := by
    simpa only [labels_length, twoBalls, Finset.union_self] using hb
  have hl := labels_work data C cost r x x
  have hnum := cdfNumerator_work data C cost (labels data r x x).value x cut N c hN hlen hK
  have hden := countLabels_work data (C + 5) (cost_mono data cost (Nat.le_add_right C 5))
    (labels data r x x).value N c hN hlen hK
  change _ + _ + _ + 3 ≤ _
  omega

theorem ideal_count_size (V : WeakSystem (Fin n) K) (B : Finset (Fin n)) (N c : ℕ)
    (hn : n ≤ N) (hK : K ≤ c * N) : Nat.size (IdealCounting.count (induced V B)) ≤ bitBound N c := by
  have hh := IdealCounting.lookup_table_size_le (induced V B) K le_rfl Finset.univ
  simp only [Fintype.card_coe] at hh
  apply hh.trans
  unfold bitBound
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul ((show B.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ B).trans hn)
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hK 1)) 1

theorem branchCounts_sizes (data : LocalDPWork.Input n K) (r : ℕ) (x y : Fin n) (N c : ℕ)
    (hn : n ≤ N) (hK : K ≤ c * N) :
    Nat.size (branchCounts data r x y).value.1 ≤ bitBound N c ∧
      Nat.size (branchCounts data r x y).value.2 ≤ bitBound N c := by
  rw [branchCounts_value]
  exact ⟨ideal_count_size _ _ N c hn hK, ideal_count_size _ _ N c hn hK⟩

theorem cdfCounts_sizes (data : LocalDPWork.Input n (K + 1)) (r : ℕ) (x : Fin n) (cut N c : ℕ)
    (hn : n ≤ N) (hK : K + 1 ≤ c * N) :
    Nat.size (cdfCounts data r x cut).value.1 ≤ bitBound N c ∧
      Nat.size (cdfCounts data r x cut).value.2 ≤ bitBound N c := by
  rw [cdfCounts_value]
  refine ⟨?_, ideal_count_size _ _ N c hn hK⟩
  cases cut with
  | zero => exact Nat.zero_le _
  | succ cut => exact ideal_count_size _ _ N c hn hK

def branchBound (n N c A : ℕ) : ℕ :=
  prepareBound n A + labelsBound n 2 + 2 * oneCountBound N c 6 + 6 * bitBound N c + 15

def cdfBound (n N c A : ℕ) : ℕ :=
  prepareBound n A + labelsBound n 2 + 2 * oneCountBound N c 7 + 6 * bitBound N c + 16

theorem branch_work (a : LocalAccess s) (A : ℕ) (cost : AccessBound a A)
    (r : ℕ) (x y : Fin n) (N c : ℕ) (hN : N ≠ 0) (hn : n ≤ N)
    (hb : (twoBalls s.rows.active x y r).card ≤ Nat.log 2 N) (hK : s.pool.palette + 1 ≤ c * N) :
    (branch a r x y).work ≤ branchBound n N c A := by
  have hp := prepare_work a A cost
  have hc := branchCounts_work (prepare a).value 2 (prepare_cost a) r x y N c hN
    (by simpa only [prepare_system, NumericalRepresentation.SourcePartition.view] using hb) hK
  simp only [Nat.reduceAdd] at hc
  have hs := branchCounts_sizes (prepare a).value r x y N c hn hK
  have hr := RationalWork.ratio_work_le (branchCounts (prepare a).value r x y).value.1
    (branchCounts (prepare a).value r x y).value.2
  change (prepare a).work + (branchCounts (prepare a).value r x y).work + _ + 2 ≤ _
  unfold branchBound
  omega

theorem cdf_work (a : LocalAccess s) (A : ℕ) (cost : AccessBound a A)
    (r : ℕ) (x : Fin n) (cut N c : ℕ) (hN : N ≠ 0) (hn : n ≤ N)
    (hb : (ball s.rows.active x r).card ≤ Nat.log 2 N) (hK : s.pool.palette + 1 ≤ c * N) :
    (cdf a r x cut).work ≤ cdfBound n N c A := by
  have hp := prepare_work a A cost
  have hc := cdfCounts_work (prepare a).value 2 (prepare_cost a) r x cut N c hN
    (by simpa only [prepare_system, NumericalRepresentation.SourcePartition.view] using hb) hK
  simp only [Nat.reduceAdd] at hc
  have hs := cdfCounts_sizes (prepare a).value r x cut N c hn hK
  have hr := RationalWork.ratio_work_le (cdfCounts (prepare a).value r x cut).value.1
    (cdfCounts (prepare a).value r x cut).value.2
  change (prepare a).work + (cdfCounts (prepare a).value r x cut).work + _ + 2 ≤ _
  unfold cdfBound
  omega

def branchPolynomial (n N c A : ℕ) : ℕ :=
  prepareBound n A + labelsBound n 2 + 2 * oneCountBound N c 6 + 6 * (N * (c * N + 2) + 1) + 15

def cdfPolynomial (n N c A : ℕ) : ℕ :=
  prepareBound n A + labelsBound n 2 + 2 * oneCountBound N c 7 + 6 * (N * (c * N + 2) + 1) + 16

theorem branchBound_le (n N c A : ℕ) : branchBound n N c A ≤ branchPolynomial n N c A := by
  have h := MeasuredLocalOracle.bitBound_polynomial N c
  unfold branchBound branchPolynomial
  omega

theorem cdfBound_le (n N c A : ℕ) : cdfBound n N c A ≤ cdfPolynomial n N c A := by
  have h := MeasuredLocalOracle.bitBound_polynomial N c
  unfold cdfBound cdfPolynomial
  omega

theorem logCap_le_double {n : ℕ} (hn : n ≠ 0) : Parameters.logCap n ≤ Nat.log 2 (2 * n) := by
  unfold Parameters.logCap
  exact Nat.log_mono_right (by omega : n + 1 ≤ 2 * n)

theorem branch_work_logCap (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (r : ℕ) (x y : Fin n) (c : ℕ) (hn : n ≠ 0)
    (hb : (twoBalls s.rows.active x y r).card ≤ Parameters.logCap n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (branch a r x y).work ≤ branchPolynomial n (2 * n) c A := by
  apply (branch_work a A hA r x y (2 * n) c (by omega) (by omega)
    (hb.trans (logCap_le_double hn))
    (hK.trans (Nat.mul_le_mul_left c (by omega : n ≤ 2 * n)))).trans
  exact branchBound_le ..

theorem cdf_work_logCap (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (r : ℕ) (x : Fin n) (cut c : ℕ) (hn : n ≠ 0)
    (hb : (ball s.rows.active x r).card ≤ Parameters.logCap n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (cdf a r x cut).work ≤ cdfPolynomial n (2 * n) c A := by
  apply (cdf_work a A hA r x cut (2 * n) c (by omega) (by omega)
    (hb.trans (logCap_le_double hn))
    (hK.trans (Nat.mul_le_mul_left c (by omega : n ≤ 2 * n)))).trans
  exact cdfBound_le ..

theorem ordinary_work_logCap (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : SeparatedPins.HasMate s.pool v)
    (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R (1 / 16))
    (c : ℕ) (hn : n ≠ 0) (hb : (ball s.rows.active v radius).card ≤ Parameters.logCap n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (MeasuredOrdinaryPromotion.atRadius a H d g R hR v hmark hv hm radius hr).work ≤
      MeasuredOrdinaryPromotion.workBound n s.pool.palette A (cdfPolynomial n (2 * n) c A) + 1 := by
  apply Nat.add_le_add_right
  exact MeasuredOrdinaryPromotion.make_work_le a hA H d g R hR v hmark hv hm _ _
    (cdfPolynomial n (2 * n) c A) (fun cut => cdf_work_logCap a hA radius v cut c hn hb hK)

theorem stopping_work_logCap (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (p : RecursiveController.Parameters)
    (ready : PassiveLocalState.Ready p.repair.scale p.repair.D p.repair.H s.pool ⟨s.rows, s.order⟩)
    (x y : Fin n) (hxy : s.pool.system.edge x y ≠ true) (hyx : s.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ colour, s.pool.pins x = some colour ∧ s.pool.pins y = some colour)
    (radius : ℕ)
    (hr : radius = p.repair.scale.H * LocalParameters.sweepCount p.repair.scale.H
      (LocalAccuracy.influenceSize p.repair.scale.H p.repair.d) p.repair.scale.R p.error)
    (c : ℕ) (hn : n ≠ 0) (hb : (twoBalls s.rows.active x y radius).card ≤ Parameters.logCap n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (MeasuredStopping.atRadius a p ready x y hxy hyx hstop radius hr).work ≤
      StoppingTestsWork.workBound n A + 2 * branchPolynomial n (2 * n) c A + 15 := by
  apply MeasuredStopping.sign_work_le a hA x y hxy hyx hstop p.error p.error_pos.le
  · change (branch a radius x y).value = LocalOracle.qBranch s.rows p.repair.scale.H p.repair.d
      p.repair.scale.R p.error x y
    rw [hr]
    exact MeasuredLocalOracle.branch_value a _ _ _ _ _ _
  · change (branch a radius y x).value = LocalOracle.qBranch s.rows p.repair.scale.H p.repair.d
      p.repair.scale.R p.error y x
    rw [hr]
    exact MeasuredLocalOracle.branch_value a _ _ _ _ _ _
  · exact branch_work_logCap a hA radius x y c hn hb hK
  · apply branch_work_logCap a hA radius y x c hn _ hK
    simpa only [twoBalls, Finset.union_comm] using hb

end SortingAdversary.Optimal.MeasuredOracleBudget
