import SortingAdversary.Optimal.ControllerEventCounts
import SortingAdversary.Optimal.UniformRates

/-!
# Concrete inverse-stage budgets for the actual controller run

The accepted runtime package fixes the degree, path, and scale parameters.
The actual incidence and reservation theorems supply their populations. Under
the proved physical cutoff, expensive mass and scale surcharge therefore
have explicit inverse-stage bounds, while all promotions are at most `8T`.
-/

namespace SortingAdversary.Optimal.UniformRunBudgets

open AsymptoticRates UniformStage ControllerMachine ControllerRun ControllerPricing
open ControllerEventCounts ReservationFinalGroups ReservationEntropyRun LedgerRun PoolTreeAccounting

variable {cap j : ℕ}

noncomputable def entropy (N : ℕ) : ℝ :=
  ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)

theorem entropy_pos (N : ℕ) : 0 < entropy N := by
  unfold entropy
  apply mul_pos
  · positivity
  · apply Real.log_pos
    exact_mod_cast (by omega : 1 < N + 2)

theorem actual_hub_mass_le (a : Accepted cap j) (hj : 0 < j) (N : ℕ)
    {final : Active a.controller (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun a.controller (initialActive a.controller N) observations final)
    (hq : (observations.length : ℝ) ≤ 4 * entropy N) :
    ((runHubs (initialActive a.controller N) observations).length : ℝ) ≤
      (12 / (j : ℝ)) * entropy N := by
  have hdegree : a.controller.repair.D = stageDegree j := a.degree
  have hpath : a.controller.repair.H = stagePathLength j := a.path
  have hscale : a.controller.repair.scale.J =
      stageScaleLength j a.controller.repair.scale.width.B := a.scale
  have hdNat := (actual_budgets a.controller N history).2
  rw [← actual_degree_count a.controller N history] at hdNat
  have hd : (j + 4 : ℝ) * (runKind (initialActive a.controller N) observations .degree : ℝ) ≤
      2 * observations.length := by
    have hh : (a.controller.repair.D : ℝ) *
        (runKind (initialActive a.controller N) observations .degree : ℝ) ≤ 2 * observations.length := by
      exact_mod_cast hdNat
    simpa only [hdegree, stageDegree, Nat.cast_add, Nat.cast_ofNat] using hh
  have budgets := actual_group_budgets a.controller N history
  have hpathCount : (runKind (initialActive a.controller N) observations .path : ℝ) ≤
      a.controller.repair.H * (historyPaths (initialActive a.controller N) observations).length := by
    exact_mod_cast run_path_le (initialActive a.controller N) observations
  have hlog : 0 ≤ Real.log (a.controller.repair.H : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by have h := a.controller.repair.path_two; omega : 1 ≤ a.controller.repair.H)
  have hp : (runKind (initialActive a.controller N) observations .path : ℝ) *
      Real.log (stagePathLength j : ℝ) ≤ entropy N := by
    have hh := mul_le_mul_of_nonneg_right hpathCount hlog
    rw [← hpath]
    unfold entropy
    nlinarith [budgets.1]
  have hs : (runKind (initialActive a.controller N) observations .scale : ℝ) *
      Real.log ((stageScaleLength j a.controller.repair.scale.width.B : ℝ) / 2) ≤ entropy N := by
    rw [← hscale, run_scale_groups, Nat.cast_mul]
    unfold entropy
    nlinarith [budgets.2]
  rw [run_hubs_eq, Nat.cast_add, Nat.cast_add]
  exact UniformAdversary.expensive_mass_le hj (entropy_pos N).le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hq hd hp hs

theorem actual_promotions_le (a : Accepted cap j) (N : ℕ)
    {final : Active a.controller (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun a.controller (initialActive a.controller N) observations final)
    (hq : (observations.length : ℝ) ≤ 4 * entropy N) :
    (promotions final.tree.erase : ℝ) ≤ 8 * entropy N := by
  have hp : (promotions final.tree.erase : ℝ) ≤ 2 * observations.length := by
    exact_mod_cast (actual_budgets a.controller N history).1
  linarith

theorem actual_hubs_le (a : Accepted cap j) (N : ℕ)
    {final : Active a.controller (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun a.controller (initialActive a.controller N) observations final)
    (hq : (observations.length : ℝ) ≤ 4 * entropy N) :
    ((runHubs (initialActive a.controller N) observations).length : ℝ) ≤ 8 * entropy N := by
  have he := actual_cheap_add_hubs a.controller N history
  have hx : (runHubs (initialActive a.controller N) observations).length ≤ promotions final.tree.erase := by omega
  have hx' : ((runHubs (initialActive a.controller N) observations).length : ℝ) ≤
      (promotions final.tree.erase : ℝ) := by exact_mod_cast hx
  exact hx'.trans (actual_promotions_le a N history hq)

theorem scaleSurcharge_eq (B : ℕ) :
    Real.log (2 * (4 : ℝ) ^ B) = stageScaleSurcharge B := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)), Real.log_pow, h4]
  unfold stageScaleSurcharge
  ring

theorem actual_scale_surcharge_le (a : Accepted cap j) (hj : 0 < j) (N : ℕ)
    {final : Active a.controller (N + 2)} {observations : History (N + 2)}
    (history : ActiveRun a.controller (initialActive a.controller N) observations final) :
    (runScale (initialActive a.controller N) observations : ℝ) *
        Real.log (2 * (4 : ℝ) ^ a.controller.repair.scale.width.B) ≤ entropy N / j := by
  have hscale : a.controller.repair.scale.J =
      stageScaleLength j a.controller.repair.scale.width.B := a.scale
  have hs := actual_scale_budget a.controller N history
  rw [hscale] at hs
  have hpositive : 0 ≤ stageScaleSurcharge a.controller.repair.scale.width.B := by
    unfold stageScaleSurcharge
    exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  rw [scaleSurcharge_eq]
  calc
    _ ≤ (entropy N / Real.log ((stageScaleLength j a.controller.repair.scale.width.B : ℝ) / 2)) *
        stageScaleSurcharge a.controller.repair.scale.width.B := mul_le_mul_of_nonneg_right hs hpositive
    _ = entropy N * (stageScaleSurcharge a.controller.repair.scale.width.B /
        Real.log ((stageScaleLength j a.controller.repair.scale.width.B : ℝ) / 2)) := by ring
    _ ≤ entropy N * (1 / (j : ℝ)) := mul_le_mul_of_nonneg_left
      (scale_surcharge_ratio_le hj _) (entropy_pos N).le
    _ = entropy N / j := by ring

end SortingAdversary.Optimal.UniformRunBudgets
