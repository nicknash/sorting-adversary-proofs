import SortingAdversary.Optimal.LedgerRun
import SortingAdversary.Optimal.CutoffBounds

/-!
# Initial and terminal counts for the actual active execution

The incidence theorem supplies the final tree's promotion count. Correct
sorting supplies totality of the actual public relation. Together they
instantiate the concrete finite-tree stars-and-bars estimate.
-/

namespace SortingAdversary.Optimal.ControllerRun

open ControllerMachine RecursiveController PoolTreeAccounting

theorem initial_log_count (p : Parameters) (N : ℕ) :
    Real.log ((initialActive p N).tree.erase.count : ℝ) =
      ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) := by
  simp only [initialActive, StoredTree.erase_initial, PoolTree.Tree.initial_count,
    Nat.cast_pow, Real.log_pow]

theorem active_terminal_bound (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {observations : History (N + 2)}
    (run : ActiveRun p (initialActive p N) observations final)
    (htotal : PoolTree.Tree.TotalOnMembers final.tree.pool)
    (hclock : (observations.length : ℝ) ≤ 4 * ((N + 2 : ℕ) : ℝ) *
      Real.log ((N + 2 : ℕ) : ℝ)) :
    Real.log (final.tree.erase.count : ℝ) ≤
      (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) *
        AsymptoticRates.terminalFraction (N + 2) := by
  have hmembers : final.tree.erase.pool.members.card = N + 2 := by
    rw [StoredTree.erase_pool, final.full]
    simp
  have hprom := (LedgerRun.actual_budgets p N run).1
  have hpromreal : (promotions final.tree.erase : ℝ) ≤ 2 * observations.length := by exact_mod_cast hprom
  have hcap : (promotions final.tree.erase : ℝ) ≤
      8 * final.tree.erase.pool.members.card * Real.log (final.tree.erase.pool.members.card : ℝ) := by
    rw [hmembers]
    nlinarith
  have hterm := TreeTerminal.normalized_terminal_of_bounded final.wellFormed final.coherent
    (by simpa only [StoredTree.erase_pool] using htotal) (by omega : 2 ≤ final.tree.erase.pool.members.card)
    final.bounded hcap
  rw [hmembers] at hterm
  have hn : (1 : ℝ) < ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < N + 2 by omega)
  have hT : 0 < (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) :=
    mul_pos (lt_trans zero_lt_one hn) (Real.log_pos hn)
  simpa only [mul_comm] using (div_le_iff₀ hT).mp hterm

end SortingAdversary.Optimal.ControllerRun

namespace SortingAdversary.Optimal.UniformAdversary

theorem selected_accepted (n : ℕ) (hj : 0 < UniformStage.selectedStage n) :
    ∃ a : UniformStage.Accepted (Parameters.logCap n) (UniformStage.selectedStage n),
      (UniformStage.choose n).decision = .accepted (UniformStage.selectedStage n) hj a := by
  have hs := UniformStage.choose_stage n
  cases he : (UniformStage.choose n).decision with
  | fallback =>
    simp only [he, UniformStage.Decision.stage] at hs
    omega
  | accepted j hj' a =>
    simp only [he, UniformStage.Decision.stage] at hs
    subst j
    exact ⟨a, rfl⟩

theorem selected_controller {n j : ℕ} {hj : 0 < j}
    (a : UniformStage.Accepted (Parameters.logCap n) j)
    (he : (UniformStage.choose n).decision = .accepted j hj a) :
    UniformStage.selectController n = some a.controller := by
  simp only [UniformStage.selectController, he]

end SortingAdversary.Optimal.UniformAdversary
