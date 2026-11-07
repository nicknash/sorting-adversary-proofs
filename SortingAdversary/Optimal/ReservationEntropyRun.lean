import SortingAdversary.Optimal.TreeReservationEntropy
import SortingAdversary.Optimal.ReservationFinalGroups

/-!
# Entropy budgets for the actual controller's path and scale groups

The hypotheses below are only the actual active execution. Group formation,
completion, disjointness, final physical destinations, and their multiplicity
bounds all come from the concrete normalizer and its stored replay.
-/

namespace SortingAdversary.Optimal.ReservationEntropyRun

open RecursiveController ControllerMachine ControllerRun ReservationRun ReservationFinalGroups
open TreeReservationEntropy PoolTreeAccounting

/-- Actual chronological reservations obey both manuscript entropy budgets. -/
theorem actual_group_budgets (p : Parameters) (N : ℕ) {observations : History (N + 2)}
    {final : Active p (N + 2)} (history : ActiveRun p (initialActive p N) observations final) :
    (((historyPaths (initialActive p N) observations).length : ℝ) * p.repair.H) *
        Real.log (p.repair.H : ℝ) ≤ ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) ∧
      (((historyScales (initialActive p N) observations).length : ℝ) * p.repair.scale.J) *
        Real.log ((p.repair.scale.J : ℝ) / 2) ≤
          ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) := by
  obtain ⟨execution, hr, hs, hp, hg⟩ := initial_final_groups p N history
  have hn : final.tree.pool.members.Nonempty := by rw [final.full]; exact Finset.univ_nonempty
  have hcard : final.tree.pool.members.card = N + 2 := by rw [final.full]; simp
  have hbPath := list_groups_root_budget final.tree final.wellFormed hn execution.books.path.groups
    hs.invariant.pathValid.disjoint hs.invariant.pathSize (by decide : 0 < 1) hp
  have hbScale := list_groups_root_budget final.tree final.wellFormed hn execution.books.scale.groups
    hs.invariant.scaleValid.disjoint hs.invariant.scaleSize (by decide : 0 < 2) hg
  obtain ⟨hpaths, hscales⟩ := replay_groups (initialActive p N) observations _ _ execution hr
  have hpathLength : execution.books.path.groups.length =
      (historyPaths (initialActive p N) observations).length := by
    rw [hs.pathGroups, hpaths]
    simp only [ReservationMachine.initial, GroupReservations.initial, List.append_nil, List.length_reverse]
  have hscaleLength : execution.books.scale.groups.length =
      (historyScales (initialActive p N) observations).length := by
    rw [hs.scaleGroups, hscales]
    simp only [ReservationMachine.initial, GroupReservations.initial, List.append_nil, List.length_reverse]
  constructor
  · simpa only [hpathLength, hcard, Nat.cast_one, div_one] using hbPath
  · simpa only [hscaleLength, hcard, Nat.cast_ofNat] using hbScale

/-- The path labels are bounded directly by their actual complete group list. -/
theorem actual_path_labels_le (p : Parameters) (N : ℕ) {observations : History (N + 2)}
    {final : Active p (N + 2)} (history : ActiveRun p (initialActive p N) observations final) :
    ((historyPaths (initialActive p N) observations).length : ℝ) * p.repair.H ≤
      (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) / Real.log (p.repair.H : ℝ) := by
  have hH : (1 : ℝ) < p.repair.H := by exact_mod_cast p.repair.path_two
  exact (le_div_iff₀ (Real.log_pos hH)).mpr (actual_group_budgets p N history).1

theorem actual_scale_labels_le (p : Parameters) (N : ℕ) {observations : History (N + 2)}
    {final : Active p (N + 2)} (history : ActiveRun p (initialActive p N) observations final)
    (hJ : 2 < p.repair.scale.J) :
    ((historyScales (initialActive p N) observations).length : ℝ) * p.repair.scale.J ≤
      (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
        Real.log ((p.repair.scale.J : ℝ) / 2) := by
  have hJ' : (2 : ℝ) < p.repair.scale.J := by exact_mod_cast hJ
  have hlog : 0 < Real.log ((p.repair.scale.J : ℝ) / 2) :=
    Real.log_pos ((one_lt_div (by norm_num : (0 : ℝ) < 2)).mpr hJ')
  exact (le_div_iff₀ hlog).mpr (actual_group_budgets p N history).2

end SortingAdversary.Optimal.ReservationEntropyRun
