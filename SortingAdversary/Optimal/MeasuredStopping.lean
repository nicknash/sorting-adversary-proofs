import SortingAdversary.Optimal.StoppingTestsWork
import SortingAdversary.Optimal.MeasuredLocalOracle
import SortingAdversary.Optimal.CalibrationWork
import SortingAdversary.Optimal.RecursiveController

/-!
# The measured actual stopping sign

The finite safety route, two actual local counting DPs and a rational cross
product comparison produce the sign. The original stopping program and its
approximation certificates occur only in erased correctness fields.
-/

namespace SortingAdversary.Optimal.MeasuredStopping

open PrimitiveWork RepresentationWork WidthRepair PoolTree.Tree ControllerRouting

variable {n : ℕ} {s : State n}

def chooseBool : Action → Bool → Bool
  | .forward, _ => true
  | .reverse, _ => false
  | .delegate, _ => false
  | .compareMasses, comparison => comparison

theorem reference_forward (p : PoolState.Pool n) (x y : Fin n)
    (hxy : p.system.edge x y ≠ true) (hyx : p.system.edge y x ≠ true)
    (hstop : ¬ ∃ c, p.pins x = some c ∧ p.pins y = some c)
    (error : ℚ) (he : 0 ≤ error) (estimates : Estimates p x y error) :
    (chooseStoppingSign p x y hxy hyx hstop error he estimates).forward =
      chooseBool (chooseRoute p.system p.pins p.invariant x y hxy hyx).val
        (decide (estimates.reverse ≤ estimates.forward)) := by
  unfold chooseStoppingSign
  dsimp only
  split
  · rename_i hd
    change true = chooseBool _ _
    rw [hd]
    rfl
  · rename_i hd
    change false = chooseBool _ _
    rw [hd]
    rfl
  · rename_i hd
    have hs := (chooseRoute p.system p.pins p.invariant x y hxy hyx).property
    rw [hd] at hs
    exact (hstop hs).elim
  · rename_i hd
    split_ifs with hc
    · change true = chooseBool _ _
      rw [hd]
      simp only [chooseBool, hc, decide_true]
    · change false = chooseBool _ _
      rw [hd]
      simp only [chooseBool, hc, decide_false]


theorem sign_ext {p : PoolState.Pool n} {x y : Fin n} {error : ℚ}
    (first second : StoppingSign p x y error) (h : first.forward = second.forward) : first = second := by
  cases first
  cases second
  dsimp only at h
  cases h
  rfl

structure Output {p : PoolState.Pool n} {x y : Fin n} {error : ℚ}
    (expected : StoppingSign p x y error) where
  sign : StoppingSign p x y error
  actual : sign = expected


theorem route_congr {K : ℕ} (S T : WeakMaps.WeakSystem (Fin n) (K + 1))
    (pins other : Fin n → Option (Fin (K + 1))) (hS : S = T) (hp : pins = other)
    (h : Invariant S pins) (h' : Invariant T other) (x y : Fin n)
    (hxy : S.edge x y ≠ true) (hyx : S.edge y x ≠ true)
    (hxy' : T.edge x y ≠ true) (hyx' : T.edge y x ≠ true) :
    (chooseRoute S pins h x y hxy hyx).val = (chooseRoute T other h' x y hxy' hyx').val := by
  cases hS
  cases hp
  rfl

def sign (a : LocalAccess s) (x y : Fin n)
    (hxy : s.pool.system.edge x y ≠ true) (hyx : s.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ c, s.pool.pins x = some c ∧ s.pool.pins y = some c)
    (error : ℚ) (he : 0 ≤ error) (estimates : Estimates s.pool x y error)
    (forward reverse : Result ℚ)
    (hf : forward.value = estimates.forward) (hr : reverse.value = estimates.reverse) :
    Result (Output (chooseStoppingSign s.pool x y hxy hyx hstop error he estimates)) := by
  let decision := StoppingTestsWork.route a.windows a.pin x y
  have hinvariant : Invariant a.windows.system (fun v => (a.pin v).value) := by
    simpa only [LocalAccess.windows_system, a.pin_value] using s.pool.invariant
  have hdecision : decision.value =
      (chooseRoute s.pool.system s.pool.pins s.pool.invariant x y hxy hyx).val := by
    have hx : a.windows.system.edge x y ≠ true := by
      simpa only [LocalAccess.windows_system] using hxy
    have hy : a.windows.system.edge y x ≠ true := by
      simpa only [LocalAccess.windows_system] using hyx
    exact (StoppingTestsWork.route_value a.windows a.pin hinvariant x y hx hy).trans
      (route_congr a.windows.system s.pool.system (fun v => (a.pin v).value) s.pool.pins
        (LocalAccess.windows_system a) (funext a.pin_value) hinvariant s.pool.invariant x y hx hy hxy hyx)
  let comparison := CalibrationWork.lessEqual reverse.value forward.value
  let chosen := chooseBool decision.value comparison.value
  have hchosen : chosen = (chooseStoppingSign s.pool x y hxy hyx hstop error he estimates).forward := by
    rw [reference_forward]
    simp only [chosen, hdecision, comparison, CalibrationWork.lessEqual_value, hf, hr]
  let result : StoppingSign s.pool x y error :=
    { forward := chosen
      safe := by rw [hchosen]; exact (chooseStoppingSign s.pool x y hxy hyx hstop error he estimates).safe
      feasible := by rw [hchosen]; exact (chooseStoppingSign s.pool x y hxy hyx hstop error he estimates).feasible
      retention := by rw [hchosen]; exact (chooseStoppingSign s.pool x y hxy hyx hstop error he estimates).retention }
  exact ⟨⟨result, sign_ext _ _ hchosen⟩,
    decision.work + forward.work + reverse.work + comparison.work + 8⟩

theorem sign_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A) (x y : Fin n)
    (hxy : s.pool.system.edge x y ≠ true) (hyx : s.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ c, s.pool.pins x = some c ∧ s.pool.pins y = some c)
    (error : ℚ) (he : 0 ≤ error) (estimates : Estimates s.pool x y error)
    (forward reverse : Result ℚ)
    (hf : forward.value = estimates.forward) (hr : reverse.value = estimates.reverse)
    (C : ℕ) (hforward : forward.work ≤ C) (hreverse : reverse.work ≤ C) :
    (sign a x y hxy hyx hstop error he estimates forward reverse hf hr).work ≤
      StoppingTestsWork.workBound n A + 2 * C + 15 := by
  have hs := StoppingTestsWork.route_work_le a.windows a.pin x y A
    hA.publicRow hA.lower hA.upper hA.pin
  change (StoppingTestsWork.route a.windows a.pin x y).work + forward.work + reverse.work + 7 + 8 ≤ _
  omega

/-- The actual ready-state estimator package is used only for its erased
accuracy proofs. Both data values come from the counted local oracle. -/
def atRadius (a : LocalAccess s) (p : RecursiveController.Parameters)
    (ready : PassiveLocalState.Ready p.repair.scale p.repair.D p.repair.H s.pool ⟨s.rows, s.order⟩)
    (x y : Fin n) (hxy : s.pool.system.edge x y ≠ true) (hyx : s.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ c, s.pool.pins x = some c ∧ s.pool.pins y = some c)
    (radius : ℕ)
    (hr : radius = p.repair.scale.H * LocalParameters.sweepCount p.repair.scale.H
      (LocalAccuracy.influenceSize p.repair.scale.H p.repair.d) p.repair.scale.R p.error) :
    Result (Output (chooseStoppingSign s.pool x y hxy hyx hstop p.error p.error_pos.le
      (NormalizedBounds.estimates ready p.repair.d p.height_old p.degree_old p.error p.error_pos
        p.comparison_minimum x y (StoredRouting.distinct_of_reverse_unknown s.pool x y hyx)))) :=
  let forward := MeasuredLocalOracle.branch a radius x y
  let reverse := MeasuredLocalOracle.branch a radius y x
  sign a x y hxy hyx hstop p.error p.error_pos.le
    (NormalizedBounds.estimates ready p.repair.d p.height_old p.degree_old p.error p.error_pos
      p.comparison_minimum x y (StoredRouting.distinct_of_reverse_unknown s.pool x y hyx))
    forward reverse
    (by
      change (MeasuredLocalOracle.branch a radius x y).value =
        LocalOracle.qBranch s.rows p.repair.scale.H p.repair.d p.repair.scale.R p.error x y
      rw [hr]
      exact MeasuredLocalOracle.branch_value a _ _ _ _ _ _)
    (by
      change (MeasuredLocalOracle.branch a radius y x).value =
        LocalOracle.qBranch s.rows p.repair.scale.H p.repair.d p.repair.scale.R p.error y x
      rw [hr]
      exact MeasuredLocalOracle.branch_value a _ _ _ _ _ _)

theorem atRadius_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (p : RecursiveController.Parameters)
    (ready : PassiveLocalState.Ready p.repair.scale p.repair.D p.repair.H s.pool ⟨s.rows, s.order⟩)
    (x y : Fin n) (hxy : s.pool.system.edge x y ≠ true) (hyx : s.pool.system.edge y x ≠ true)
    (hstop : ¬ ∃ c, s.pool.pins x = some c ∧ s.pool.pins y = some c)
    (radius : ℕ)
    (hr : radius = p.repair.scale.H * LocalParameters.sweepCount p.repair.scale.H
      (LocalAccuracy.influenceSize p.repair.scale.H p.repair.d) p.repair.scale.R p.error)
    (c : ℕ) (hn : n ≠ 0)
    (hb : (BallSchedule.twoBalls s.rows.active x y radius).card ≤ Nat.log 2 n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (atRadius a p ready x y hxy hyx hstop radius hr).work ≤
      StoppingTestsWork.workBound n A + 2 * MeasuredLocalOracle.branchBound n c A + 15 := by
  apply sign_work_le a hA x y hxy hyx hstop p.error p.error_pos.le
  · change (MeasuredLocalOracle.branch a radius x y).value =
      LocalOracle.qBranch s.rows p.repair.scale.H p.repair.d p.repair.scale.R p.error x y
    rw [hr]
    exact MeasuredLocalOracle.branch_value a _ _ _ _ _ _
  · change (MeasuredLocalOracle.branch a radius y x).value =
      LocalOracle.qBranch s.rows p.repair.scale.H p.repair.d p.repair.scale.R p.error y x
    rw [hr]
    exact MeasuredLocalOracle.branch_value a _ _ _ _ _ _
  · exact MeasuredLocalOracle.branch_work a A hA radius x y c hn hb hK
  · apply MeasuredLocalOracle.branch_work a A hA radius y x c hn _ hK
    simpa only [BallSchedule.twoBalls, Finset.union_comm] using hb

end SortingAdversary.Optimal.MeasuredStopping
