import SortingAdversary.Optimal.ControllerRun

/-!
# Bounds for the implemented physical clock

The integer cutoff dominates the leading-one target at every nontrivial
input size. Its actual value is eventually at most `4 * n * log n`, which
supplies the finite incidence budget used by the terminal and price bounds.
-/

namespace SortingAdversary.Optimal.UniformAdversary

open Filter
open scoped Topology

theorem logCap_le_log_div (n : ℕ) :
    (Parameters.logCap n : ℝ) ≤ Real.log ((n : ℝ) + 1) / Real.log 2 := by
  have hp : (2 : ℝ) ^ Parameters.logCap n ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Parameters.logCap n) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

theorem log_div_le_logCap_succ {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) / Real.log 2 ≤ (Parameters.logCap n : ℝ) + 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (n : ℝ) + 1 < (2 : ℝ) ^ (Parameters.logCap n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + 1)
  have hl := Real.log_le_log hnpos (show (n : ℝ) ≤ 2 ^ (Parameters.logCap n + 1) by linarith)
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hl
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

theorem nLog2n_le_cutoff {n : ℕ} (hn : 2 ≤ n) : nLog2n n ≤ (cutoff n : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (log_div_le_logCap_succ hn) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hc : (0 : ℝ) ≤ (n : ℝ) * ((Parameters.logCap n : ℝ) + 1) := by positivity
  unfold nLog2n cutoff
  push_cast
  nlinarith

theorem cutoff_ratio_le {n : ℕ} (hn : 2 ≤ n) :
    (cutoff n : ℝ) / ((n : ℝ) * Real.log n) ≤
      (2 / Real.log 2) * (Real.log ((n : ℝ) + 1) / Real.log n) + 2 / Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := mul_le_mul_of_nonneg_left (logCap_le_log_div n) (show (0 : ℝ) ≤ 2 * n by positivity)
  apply (div_le_iff₀ (mul_pos hnpos hnlog)).mpr
  have he : ((2 / Real.log 2) * (Real.log ((n : ℝ) + 1) / Real.log n) + 2 / Real.log n) *
      ((n : ℝ) * Real.log n) = 2 * n * (Real.log ((n : ℝ) + 1) / Real.log 2) + 2 * n := by
    field_simp
  rw [he]
  unfold cutoff
  push_cast
  nlinarith

theorem cutoff_eventually_le : ∀ᶠ n : ℕ in atTop,
    (cutoff n : ℝ) ≤ 4 * n * Real.log n := by
  have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at h
    linarith
  have hlim : Tendsto (fun n : ℕ =>
      (2 / Real.log 2) * (Real.log ((n : ℝ) + 1) / Real.log n) + 2 / Real.log n)
      atTop (𝓝 (2 / Real.log 2)) := by
    simpa using (AsymptoticRates.log_succ_div_log_tendsto.const_mul (2 / Real.log 2)).add
      (tendsto_const_nhds.div_atTop AsymptoticRates.log_nat_tendsto :
        Tendsto (fun n : ℕ => (2 : ℝ) / Real.log n) atTop (𝓝 0))
  have hlt : (2 : ℝ) / Real.log 2 < 4 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  filter_upwards [(tendsto_order.mp hlim).2 4 hlt, eventually_ge_atTop 2] with n hn hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h := (cutoff_ratio_le hn2).trans hn.le
  have he := (div_le_iff₀ (mul_pos hnpos hnlog)).mp h
  nlinarith

end SortingAdversary.Optimal.UniformAdversary
