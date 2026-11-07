import SortingAdversary.Optimal.UniformStage
import SortingAdversary.Optimal.RecursiveController

/-!
# Instantiating the recursive controller from the bounded stage scan

There are no remaining local-accuracy or normalization hypotheses in this
adapter. Its accepted input is the concrete capped stage constructor's own
output. Stage zero remains the explicit finite-size fallback branch.
-/

namespace SortingAdversary.Optimal.UniformStage

def controllerParameters (r : StageParameters.Runtime) : RecursiveController.Parameters where
  repair := r.normalizer
  error := r.ε
  error_pos := r.error_pos
  error_small := r.error_small
  height_budget := r.height_budget
  degree_budget := r.degree_budget
  comparable_budget := r.comparable_budget
  comparison_minimum := r.comparison_minimum

def Accepted.controller {cap j : ℕ} (a : Accepted cap j) : RecursiveController.Parameters :=
  controllerParameters a.runtime

theorem Accepted.comparisonBall_cap {cap j : ℕ} (a : Accepted cap j) :
    LocalOracleWork.comparisonBallBound a.controller.repair.scale.H a.controller.repair.d
      a.controller.repair.scale.R a.controller.error ≤ cap := by
  change LocalOracleWork.comparisonBallBound a.runtime.normalizer.scale.H a.runtime.normalizer.d
    a.runtime.normalizer.scale.R a.runtime.ε ≤ cap
  rw [← a.runtime.comparisonBall_eq]
  exact a.comparison_ball

theorem Accepted.cdfBall_cap {cap j : ℕ} (a : Accepted cap j) :
    LocalOracleWork.cdfBallBound a.controller.repair.scale.H a.controller.repair.d
      a.controller.repair.scale.R (1 / 16) ≤ cap := by
  change LocalOracleWork.cdfBallBound a.runtime.normalizer.scale.H a.runtime.normalizer.d
    a.runtime.normalizer.scale.R (1 / 16) ≤ cap
  rw [← a.runtime.cdfBall_eq]
  exact a.cdf_ball

/-- The externally callable uniform selector, including its explicit
fallback result for inputs too small to admit the first positive stage. -/
def selectController (n : ℕ) : Option RecursiveController.Parameters :=
  match (choose n).decision with
  | .fallback => none
  | .accepted _ _ a => some a.controller

theorem selectController_isSome (n : ℕ) :
    (selectController n).isSome = true ↔ 0 < selectedStage n := by
  have hs := choose_stage n
  unfold selectController
  cases h : (choose n).decision with
  | fallback =>
    simp only [h, Decision.stage] at hs
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    omega
  | accepted j hj a =>
    simp only [h, Decision.stage] at hs
    simp only [Option.isSome_some, true_iff]
    omega

theorem selectController_eventually :
    ∀ᶠ n in Filter.atTop, (selectController n).isSome = true := by
  filter_upwards [selectedStage_tendsto.eventually (Filter.eventually_gt_atTop 0)] with n hn
  exact (selectController_isSome n).mpr hn

end SortingAdversary.Optimal.UniformStage
