import SortingAdversary.Optimal.ActiveTerminal
import SortingAdversary.Optimal.UniformRates

/-!
# Recovering the actual selected controller execution

The bounded selector's successful package determines the concrete family
member. Below the actual physical cutoff, a correct sorting tree produces
the full active-run witness and totality of its real terminal public order.
-/

namespace SortingAdversary.Optimal.UniformAdversary

open RecursiveController ControllerMachine ControllerRun

theorem selectedCheap_eq {n j : ℕ} {hj : 0 < j}
    (a : UniformStage.Accepted (Parameters.logCap n) j)
    (he : (UniformStage.choose n).decision = .accepted j hj a) :
    selectedCheap n = a.runtime.cheap := by simp only [selectedCheap, he]

theorem selectedStage_eq {n j : ℕ} {hj : 0 < j}
    (a : UniformStage.Accepted (Parameters.logCap n) j)
    (he : (UniformStage.choose n).decision = .accepted j hj a) :
    UniformStage.selectedStage n = j := by
  have h := UniformStage.choose_stage n
  simpa only [he, UniformStage.Decision.stage] using h.symm

theorem selected_strategy {N j : ℕ} {hj : 0 < j}
    (a : UniformStage.Accepted (Parameters.logCap (N + 2)) j)
    (he : (UniformStage.choose (N + 2)).decision = .accepted j hj a) :
    strategy (N + 2) = (ControllerMachine.machine a.controller N (cutoff (N + 2))).strategy := by
  unfold strategy
  rw [machine_of_admitted N a.controller (selected_controller a he)]

theorem selected_activeRun {N j : ℕ} {hj : 0 < j}
    (a : UniformStage.Accepted (Parameters.logCap (N + 2)) j)
    (he : (UniformStage.choose (N + 2)).decision = .accepted j hj a)
    (t : DecisionTree (N + 2)) (ht : t.Correct)
    (hclock : (t.run (strategy (N + 2)) []).comparisons ≤ cutoff (N + 2)) :
    ∃ final : Active a.controller (N + 2),
      ActiveRun a.controller (initialActive a.controller N)
        (t.run (strategy (N + 2)) []).observations final ∧
      PoolTree.Tree.TotalOnMembers final.tree.pool := by
  rw [selected_strategy a he] at hclock ⊢
  rcases active_or_cutoff a.controller N (cutoff (N + 2)) t with hb | ⟨final, run, _, hfinal⟩
  · omega
  · exact ⟨final, run, active_terminal_total a.controller N (cutoff (N + 2)) t ht final hfinal⟩

end SortingAdversary.Optimal.UniformAdversary
