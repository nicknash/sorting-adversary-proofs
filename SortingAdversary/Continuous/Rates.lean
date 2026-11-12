import SortingAdversary.Continuous.Accounting
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Vanishing overhead for the continuous prefix bound

These limits concern the actual expression `prefixOverhead` proved in the
accounting module. They are independent of the input size, transcript, and
target partial order. A parameter-generation program must separately prove
that its selected stages tend to infinity.
-/

namespace SortingAdversary.Continuous

open Filter
open scoped Topology

theorem stopMass_tendsto : Tendsto stopMass atTop (𝓝 1) := by
  have hi : Tendsto (fun k : ℝ => 1 / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  change Tendsto (fun k : ℝ => 1 - 1 / k) atTop (𝓝 1)
  simpa only [sub_zero] using (tendsto_const_nhds.sub hi :
    Tendsto (fun k : ℝ => 1 - 1 / k) atTop (𝓝 (1 - 0)))

theorem stopCost_tendsto : Tendsto stopCost atTop (𝓝 0) := by
  have hl := (stopMass_tendsto.log (by norm_num : (1 : ℝ) ≠ 0)).div_const (Real.log 2)
  change Tendsto (fun k : ℝ => -(Real.log (stopMass k) / Real.log 2)) atTop (𝓝 0)
  simpa using hl.neg

theorem answerRetained_tendsto : Tendsto answerRetained atTop (𝓝 (1 / 2)) := by
  have hi : Tendsto (fun k : ℝ => 1 / (100 * k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 100) tendsto_id)
  change Tendsto (fun k : ℝ => 1 / 2 - 1 / (100 * k)) atTop (𝓝 (1 / 2))
  simpa only [sub_zero] using (tendsto_const_nhds.sub hi :
    Tendsto (fun k : ℝ => 1 / 2 - 1 / (100 * k)) atTop (𝓝 (1 / 2 - 0)))

theorem answerLoss_tendsto : Tendsto answerLoss atTop (𝓝 1) := by
  have hl := (answerRetained_tendsto.log
    (by norm_num : (1 / 2 : ℝ) ≠ 0)).div_const (Real.log 2)
  have heq : -(Real.log (1 / 2) / Real.log 2) = (1 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    field_simp
    ring
  change Tendsto (fun k : ℝ => -(Real.log (answerRetained k) / Real.log 2)) atTop (𝓝 1)
  simpa only [heq] using hl.neg

theorem tariffSlope_tendsto : Tendsto tariffSlope atTop (𝓝 1) := by
  have hnum := stopCost_tendsto.const_add 1
  have hdiv := hnum.div stopMass_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k : ℝ => (1 + stopCost k) / stopMass k) atTop (𝓝 1)
  simp only [add_zero, div_one] at hdiv
  convert hdiv using 1
  ext k
  rfl

theorem log2_div_self_tendsto :
    Tendsto (fun k : ℝ => log2 k / k) atTop (𝓝 0) := by
  have hl : Tendsto (fun k : ℝ => Real.log k / k) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hs := hl.div_const (Real.log 2)
  have hs' : Tendsto (fun k : ℝ => Real.log k / k / Real.log 2) atTop (𝓝 0) := by
    simpa using hs
  apply hs'.congr' (Filter.Eventually.of_forall (fun k => ?_))
  unfold log2
  ring

theorem tariffIntercept_div_tendsto :
    Tendsto (fun k : ℝ => tariffIntercept k / k) atTop (𝓝 0) := by
  have ha := tariffSlope_tendsto.div_atTop (tendsto_id : Tendsto (fun k : ℝ => k) atTop atTop)
  have hsum := (ha.const_mul 4).add (log2_div_self_tendsto.const_mul 2)
  have hsum' : Tendsto (fun k : ℝ => 4 * (tariffSlope k / k) + 2 * (log2 k / k))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum'.congr' (Filter.Eventually.of_forall (fun k => ?_))
  unfold tariffIntercept
  ring

/-- The continuous construction's explicitly defined prefix overhead tends
to zero. This does not use the earlier colour adversary's rate theorem. -/
theorem prefixOverhead_tendsto : Tendsto prefixOverhead atTop (𝓝 0) := by
  have h := (((tariffSlope_tendsto.mul answerLoss_tendsto).sub_const 1).add
    (stopCost_tendsto.const_mul 2)).add (tariffIntercept_div_tendsto.const_mul 8)
  have h' : Tendsto (fun k : ℝ => (tariffSlope k * answerLoss k - 1) +
      2 * stopCost k + 8 * (tariffIntercept k / k)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, one_mul, sub_self, mul_zero, add_zero] using h
  change Tendsto (fun k : ℝ => prefixOverhead k) atTop (𝓝 0)
  apply h'.congr' (Filter.Eventually.of_forall (fun k => ?_))
  unfold prefixOverhead
  ring

theorem prefixOverhead_nat_tendsto :
    Tendsto (fun k : ℕ => prefixOverhead k) atTop (𝓝 0) :=
  prefixOverhead_tendsto.comp tendsto_natCast_atTop_atTop

/-- Any divergent stage schedule has the same vanishing prefix overhead. -/
theorem selected_overhead_tendsto (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop) :
    Tendsto (fun n => prefixOverhead (stage n)) atTop (𝓝 0) :=
  prefixOverhead_nat_tendsto.comp hstage

theorem selected_error_tendsto (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop) :
    Tendsto (fun n => prefixOverhead (stage n) / (1 + prefixOverhead (stage n)))
      atTop (𝓝 0) := by
  have h := selected_overhead_tendsto stage hstage
  have hd := h.div (h.const_add 1) (by norm_num : (1 + 0 : ℝ) ≠ 0)
  simp only [add_zero, zero_div] at hd
  convert hd using 1
  ext n
  rfl

end SortingAdversary.Continuous
