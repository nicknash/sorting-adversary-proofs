import SortingAdversary.Optimal.ControllerFinalPrice
import SortingAdversary.Optimal.TreePriceEntropy

/-!
# The actual complete run has a uniform dictionary budget

The final dictionary's capacity and selected entropy are bounded by the real
tree populations. The accepted incidence ledger bounds those populations by
twice the actual query count. No stage-dependent constant enters this bound.
-/

namespace SortingAdversary.Optimal.ControllerFinalPrice

open scoped BigOperators
open WidthRepair PoolState PoolTreeAccounting StoredStateIndex
open RecursiveController ControllerMachine ControllerRun ControllerPricing RepairPricing
open IndexedHubHistory SlotHubHistory TreePriceBudget

theorem actual_budget_bounds (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {history : History (N + 2)}
    (run : ActiveRun p (initialActive p N) history final)
    (clock : (history.length : ℝ) ≤
      4 * (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ))) :
    0 ≤ hubBudget final.tree (runHubs (initialActive p N) history) ∧
      hubBudget final.tree (runHubs (initialActive p N) history) ≤
        256 * (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) := by
  let hubs := runHubs (initialActive p N) history
  let actual := events final.tree hubs
  let allocated := (LedgerRun.initial_spec p N run).allocated
  have hf : AtFinal final.tree hubs := runHubs_fit run
  have fits := events_fits final.tree allocated hubs hf
  have unique := events_locations_injective final.tree allocated hubs hf
    (ControllerLedgerAlignment.actual_hub_locations_nodup p N run)
  have bounded : ∀ c, SlotHubHistory.count final.tree actual c ≤ population final.tree c :=
    count_le_population final.tree actual fits unique
  have hc : final.tree.pool.members.card = N + 2 := by rw [final.full]; simp
  have hP : (promotions final.tree.erase : ℝ) ≤
      8 * (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) := by
    have h : (promotions final.tree.erase : ℝ) ≤ 2 * (history.length : ℝ) := by
      exact_mod_cast (LedgerRun.actual_budgets p N run).1
    linarith
  have hX : (∑ c : Slot final.tree, (SlotHubHistory.count final.tree actual c : ℝ)) ≤
      8 * (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) := by
    have hs : (∑ c : Slot final.tree, (SlotHubHistory.count final.tree actual c : ℝ)) = hubs.length := by
      exact_mod_cast count_sum final.tree actual fits
    rw [hs]
    have hp : (hubs.length : ℝ) ≤ promotions final.tree.erase := by
      exact_mod_cast (show hubs.length ≤ promotions final.tree.erase from by
        have h := ControllerEventCounts.actual_cheap_add_hubs p N run
        dsimp only [hubs]
        omega)
    exact hp.trans hP
  constructor
  · exact dictionaryBudget_nonneg final.tree _ bounded
  · have h := dictionaryBudget_le final.tree final.wellFormed (by rw [hc]; omega)
      final.bounded (SlotHubHistory.count final.tree actual) bounded
      (by simpa only [hc] using hP) (by simpa only [hc] using hX)
    change dictionaryBudget final.tree (SlotHubHistory.count final.tree actual) ≤ _
    simpa only [hc] using h

end SortingAdversary.Optimal.ControllerFinalPrice
