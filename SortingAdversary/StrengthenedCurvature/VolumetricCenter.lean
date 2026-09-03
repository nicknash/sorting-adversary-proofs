import SortingAdversary.StrengthenedCurvature.Endpoints
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Volumetric centers

This file separates the order-theoretic facts about the optimized potential
from the analytic existence and stationarity theorem.  A center is an actual
minimizer of the natural-log volumetric value on the open history polytope.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- An interior placement attaining the volumetric minimum for a history. -/
def IsVolumetricCenter (h : History n) (x : Placement n) : Prop :=
  InHistoryPolytope h x ∧
    ∀ y : Placement n, InHistoryPolytope h y →
      volumetricValue h x ≤ volumetricValue h y

namespace IsVolumetricCenter

variable {n : ℕ} {h : History n} {x : Placement n}

theorem value₂_le (hc : IsVolumetricCenter h x) {y : Placement n}
    (hy : InHistoryPolytope h y) :
    volumetricValue₂ h x ≤ volumetricValue₂ h y := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact (div_le_div_iff_of_pos_right hlogtwo).2 (hc.2 y hy)

/-- At a genuine center the `sInf` definition of the history potential is
attained. -/
theorem historyPotential_eq (hc : IsVolumetricCenter h x) :
    historyPotential h = volumetricValue₂ h x := by
  apply le_antisymm
  · exact historyPotential_le_value hc.1
  · rw [historyPotential]
    apply le_csInf
    · exact ⟨volumetricValue₂ h x, x, hc.1, rfl⟩
    rintro z ⟨y, hy, rfl⟩
    exact value₂_le hc hy

theorem natural_historyPotential_eq (hc : IsVolumetricCenter h x) :
    Real.log 2 * historyPotential h = volumetricValue h x := by
  rw [historyPotential_eq hc, volumetricValue₂]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

end IsVolumetricCenter

end StrengthenedCurvature
end SortingAdversary
