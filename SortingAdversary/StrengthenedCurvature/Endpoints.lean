import SortingAdversary.StrengthenedCurvature.Barrier
import SortingAdversary.StrengthenedCurvature.DeterminantOrder
import SortingAdversary.StrengthenedCurvature.TerminalEndpoint
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Initial and terminal volumetric endpoints

This file proves the endpoint estimates which turn a local determinant bound
into an `n log n` comparison lower bound.
 -/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

/-- The symmetric point of the initial cube. -/
noncomputable def midpointPlacement (n : ℕ) : Placement n := fun _ => 1 / 2

@[simp] theorem midpointPlacement_apply (v : Item n) :
    midpointPlacement n v = (1 / 2 : ℝ) := rfl

theorem midpointPlacement_mem :
    InHistoryPolytope ([] : History n) (midpointPlacement n) := by
  constructor
  · intro v
    norm_num [midpointPlacement]
  · simp

theorem initial_hessian_det_midpoint :
    (barrierHessian ([] : History n) (midpointPlacement n)).det = 8 ^ n := by
  rw [barrierHessian_nil_eq_diagonal, Matrix.det_diagonal]
  norm_num [midpointPlacement]

theorem initial_volumetricValue₂_midpoint :
    volumetricValue₂ ([] : History n) (midpointPlacement n) =
      (3 / 2 : ℝ) * n := by
  have hlogtwo : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [volumetricValue₂, volumetricValue, initial_hessian_det_midpoint,
    Real.log_pow]
  have hlogeight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlogeight]
  field_simp

private theorem initial_det_one_le {x : Placement n} (hx : InUnitBox x) :
    1 ≤ (barrierHessian ([] : History n) x).det := by
  rw [barrierHessian_nil_eq_diagonal, Matrix.det_diagonal]
  apply Finset.one_le_prod
  intro v _
  have hxpos : 0 < x v := (hx v).1
  have hxle : x v ≤ 1 := (hx v).2.le
  have hsqpos : 0 < x v ^ 2 := sq_pos_of_pos hxpos
  have hsqle : x v ^ 2 ≤ 1 := by nlinarith
  have hone : 1 ≤ 1 / x v ^ 2 := one_le_one_div hsqpos hsqle
  have hother : 0 ≤ 1 / (1 - x v) ^ 2 := by positivity
  linarith

private theorem initial_value_nonneg {x : Placement n} (hx : InUnitBox x) :
    0 ≤ volumetricValue₂ ([] : History n) x := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogdet : 0 ≤ Real.log (barrierHessian ([] : History n) x).det :=
    Real.log_nonneg (initial_det_one_le hx)
  exact div_nonneg (mul_nonneg (by norm_num) hlogdet) hlogtwo.le

theorem initial_values_bddBelow :
    BddBelow (volumetricValue₂ ([] : History n) ''
      {x | InHistoryPolytope ([] : History n) x}) := by
  refine ⟨0, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact initial_value_nonneg hx.1

/-- The initial volumetric potential is at most `3n/2` (in fact equality
holds, but the upper bound is exactly what global telescoping needs). -/
theorem historyPotential_nil_upper :
    historyPotential ([] : History n) ≤ (3 / 2 : ℝ) * n := by
  calc
    historyPotential ([] : History n) ≤
        volumetricValue₂ ([] : History n) (midpointPlacement n) := by
      apply csInf_le initial_values_bddBelow
      exact ⟨midpointPlacement n, midpointPlacement_mem, rfl⟩
    _ = (3 / 2 : ℝ) * n := initial_volumetricValue₂_midpoint

/-- Every feasible Hessian has determinant at least one.  This supplies the
uniform lower bound needed to use the infimum definition of the potential at
arbitrary histories. -/
theorem barrierHessian_det_one_le {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) : 1 ≤ (barrierHessian h x).det := by
  rw [barrierHessian_eq_lower_add]
  have hlower : 1 ≤ (lowerBoxHessian x).det := by
    rw [lowerBoxHessian_eq_diagonal, Matrix.det_diagonal]
    apply Finset.one_le_prod
    intro v _
    have hxpos : 0 < x v := (hx.1 v).1
    have hxle : x v ≤ 1 := (hx.1 v).2.le
    have hsqpos : 0 < x v ^ 2 := sq_pos_of_pos hxpos
    have hsqle : x v ^ 2 ≤ 1 := by nlinarith
    exact one_le_one_div hsqpos hsqle
  exact hlower.trans (det_le_det_add_of_posDef_of_posSemidef
    (lowerBoxHessian_posDef hx.1) (hessianTerms_posSemidef _ x))

theorem volumetricValue₂_nonneg {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) : 0 ≤ volumetricValue₂ h x := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogdet : 0 ≤ Real.log (barrierHessian h x).det :=
    Real.log_nonneg (barrierHessian_det_one_le hx)
  exact div_nonneg (mul_nonneg (by norm_num) hlogdet) hlogtwo.le

theorem historyValues_bddBelow (h : History n) :
    BddBelow (volumetricValue₂ h '' {x | InHistoryPolytope h x}) := by
  refine ⟨0, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact volumetricValue₂_nonneg hx

/-- The optimized potential is no larger than its value at any feasible
placement. -/
theorem historyPotential_le_value {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) :
    historyPotential h ≤ volumetricValue₂ h x := by
  apply csInf_le (historyValues_bddBelow h)
  exact ⟨x, hx, rfl⟩

theorem historyPotential_nonneg (h : History n) (π : Ranking n)
    (hπ : Compatible π h) : 0 ≤ historyPotential h := by
  apply le_csInf
  · exact ⟨volumetricValue₂ h (rankingPlacement π),
      rankingPlacement π, rankingPlacement_mem π h hπ, rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact volumetricValue₂_nonneg hx

/-- A history which determines a unique ranking has optimized terminal
potential at least `n log₂ n`. -/
theorem historyPotential_terminal_lower (h : History n) (π : Ranking n)
    (hπ : Compatible π h)
    (hunique : ∀ τ : Ranking n, Compatible τ h → τ = π) :
    nLog2n n ≤ historyPotential h := by
  cases n with
  | zero =>
      simpa [nLog2n] using historyPotential_nonneg h π hπ
  | succ m =>
      apply le_csInf
      · exact ⟨volumetricValue₂ h (rankingPlacement π),
          rankingPlacement π, rankingPlacement_mem π h hπ, rfl⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact terminal_volumetricValue₂_lower h π hπ hunique (by omega) x hx

/-- The retained reverse-chronological history at a correct leaf still
determines the output ranking, so it satisfies the terminal endpoint. -/
theorem retained_terminal_potential_lower (t : DecisionTree n)
    (strategy : Strategy n) (ht : t.Correct) (π : Ranking n)
    (hπ : Compatible π (t.run strategy []).observations) :
    nLog2n n ≤ historyPotential
      (retainedHistory (t.run strategy []).observations.reverse) := by
  let h := retainedHistory (t.run strategy []).observations.reverse
  have hπrev : Compatible π (t.run strategy []).observations.reverse := by
    simpa [Compatible, List.forall_iff_forall_mem] using hπ
  have hπret : Compatible π h :=
    compatible_retainedHistory π _ hπrev
  apply historyPotential_terminal_lower h π hπret
  intro τ hτ
  have hτrev : Compatible τ (t.run strategy []).observations.reverse :=
    (compatible_retainedHistory_iff τ _).1 hτ
  have hτchron : Compatible τ (t.run strategy []).observations := by
    simpa [Compatible, List.forall_iff_forall_mem] using hτrev
  exact compatible_unique_of_correct_run t strategy ht hτchron hπ

end StrengthenedCurvature
end SortingAdversary
