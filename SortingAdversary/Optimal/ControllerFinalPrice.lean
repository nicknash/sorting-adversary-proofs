import SortingAdversary.Optimal.SlotHubHistory
import SortingAdversary.Optimal.ControllerEventCounts
import SortingAdversary.Optimal.CheapHubPrice

/-!
# The actual complete run satisfies the signed global price bound

All prices here are extracted from the concrete controller. Cheap and hub
admissions share each actual child factorial, scale surcharges are counted
exactly, and the expensive bound uses one final dictionary for all hub kinds.
-/

namespace SortingAdversary.Optimal.ControllerFinalPrice

open scoped BigOperators
open WidthRepair PoolState PoolTreeAccounting StoredStateIndex TreeChronology
open RecursiveController ControllerMachine ControllerRun ControllerPricing RepairPricing
open IndexedHubHistory SlotHubHistory TreePriceBudget TreeFactorialCredit

variable {n : ℕ}

noncomputable def hubBudget (tree : StoredTree n) (history : List (ℕ × HubEvent n)) : ℝ :=
  (DyadicDictionary.totalCapacity (exponent tree) : ℝ) +
    ∑ c : Slot tree, (SlotHubHistory.count tree (events tree history) c : ℝ) *
      Real.log ((2 : ℝ) ^ exponent tree c.1 / SlotHubHistory.count tree (events tree history) c)

theorem cheapCharge_pos (p : WidthParameters) : (0 : ℝ) < p.cheapCharge := by
  have hW : 0 < p.W₀ := lt_of_lt_of_le (by decide : 0 < 32) p.large
  unfold WidthParameters.cheapCharge
  push_cast
  positivity

/-- No pricing, population, oracle, or retention estimate is supplied by the
caller: the sole premise is an actual run of the concrete controller. -/
theorem actual_price (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {history : History (N + 2)}
    (run : ActiveRun p (initialActive p N) history final) :
    ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) - Real.log (final.tree.erase.count : ℝ) ≤
      (history.length : ℝ) * LedgerControllerPrices.physicalPrice p +
      runCuts (initialActive p N) history * Real.log (p.repair.scale.width.cutCharge : ℝ) +
      2 * (N + 2 : ℕ) * (p.repair.scale.width.cheapCharge : ℝ) +
      SignedPrice.priceCoefficient (Real.exp 1 * 128) *
        SignedPrice.entropyEnvelope (runHubs (initialActive p N) history).length
          (hubBudget final.tree (runHubs (initialActive p N) history)) +
      runScale (initialActive p N) history * Real.log (2 * (4 : ℝ) ^ p.repair.scale.width.B) := by
  let hubs := runHubs (initialActive p N) history
  let actual := events final.tree hubs
  let allocation := (LedgerRun.initial_spec p N run).allocated
  have finalFits : AtFinal final.tree hubs := runHubs_fit run
  have fits : ∀ i, (actual i).2.Fits (stateAt final.tree (actual i).1) :=
    events_fits final.tree allocation hubs finalFits
  have unique : Function.Injective (fun i => ((actual i).1, (actual i).2.vertex)) :=
    events_locations_injective final.tree allocation hubs finalFits
      (ControllerLedgerAlignment.actual_hub_locations_nodup p N run)
  have bounded : ∀ c, SlotHubHistory.count final.tree actual c ≤ population final.tree c :=
    count_le_population final.tree actual fits unique
  have mass : runCheap (initialActive p N) history +
      (∑ c ∈ TreePriceBudget.destinations final.tree, SlotHubHistory.count final.tree actual c) =
      ∑ c ∈ TreePriceBudget.destinations final.tree, population final.tree c := by
    rw [occupied_sum final.tree actual bounded (fun k => k) rfl,
      TreePriceBudget.sum_destinations final.tree (fun k => k) rfl]
    rw [count_sum final.tree actual fits, total_population final.tree final.wellFormed]
    exact ControllerEventCounts.actual_cheap_add_hubs p N run
  let units := (hubs.map (hubPrice (exponentByIdentity final.tree (exponent final.tree)))).sum
  have split := CheapHubPrice.split_debit_of_mass (TreePriceBudget.destinations final.tree)
    (population final.tree) (SlotHubHistory.count final.tree actual) (fun c _ => bounded c)
    (runCheap (initialActive p N) history) mass (p.repair.scale.width.cheapCharge : ℝ) units
    (cheapCharge_pos p.repair.scale.width)
  rw [TreePriceBudget.sum_destinations final.tree (fun k => Real.log (k.factorial : ℝ)) (by simp),
    factorial_sum final.tree final.wellFormed,
    occupied_sum final.tree actual bounded (fun k => Real.log (k.factorial : ℝ)) (by simp)] at split
  have dictionary := actual_signed_hubs p N run (exponent final.tree) (exponent_covers final.tree)
  change (∑ i, (actual i).2.unitPrice (exponent final.tree (actual i).1)) -
      (∑ c ∈ GlobalHistory.destinations actual, Real.log ((GlobalHistory.countAt actual c).factorial : ℝ)) ≤ _
    at dictionary
  rw [factorial_sum_keys final.tree actual fits, entropy_sum_keys final.tree actual fits,
    price_sum final.tree hubs (exponent final.tree)] at dictionary
  have priced := run_priced (initialActive p N) history
    (exponentByIdentity final.tree (exponent final.tree))
    (run_record_capacity run allocation (exponent final.tree) (exponent_covers final.tree))
  have signed := ControllerLedgerAlignment.actual_signed p N run
  have nonempty : final.tree.pool.members.Nonempty := by rw [final.full]; exact Finset.univ_nonempty
  have card := destination_card_le final.tree final.wellFormed nonempty
  rw [final.full, Finset.card_univ, Fintype.card_fin] at card
  have small : (TreePriceBudget.destinations final.tree).card * (p.repair.scale.width.cheapCharge : ℝ) ≤
      2 * (N + 2 : ℕ) * (p.repair.scale.width.cheapCharge : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (cheapCharge_pos p.repair.scale.width).le
    exact_mod_cast card
  change units - _ ≤ SignedPrice.priceCoefficient (Real.exp 1 * 128) *
    SignedPrice.entropyEnvelope hubs.length (hubBudget final.tree hubs) at dictionary
  dsimp only [units, hubs] at split dictionary
  linarith

end SortingAdversary.Optimal.ControllerFinalPrice
