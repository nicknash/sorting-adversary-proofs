import SortingAdversary.Optimal.ControllerPricing

/-!
# Summed prices of the actual controller's emitted records

Each record is priced using the final capacity of its immutable parent node.
The real debit is separated into cheap pins, actual cuts, the common dyadic
hub tariff, and the exact count of scale surcharges.
-/

namespace SortingAdversary.Optimal.ControllerPricing

open WidthRepair RecursiveController ControllerMachine RepairPricing

variable {n : ℕ} {p : Parameters}

noncomputable def hubPrice (exponent : ℕ → ℕ) (tagged : ℕ × HubEvent n) : ℝ :=
  tagged.2.unitPrice (exponent tagged.1)

theorem record_priced (record : RepairRecord p n) (exponent : ℕ → ℕ)
    (cap : record.result.final.pool.palette + 1 ≤ 2 ^ exponent record.identity) :
    logCharge record.result.trace ≤
      (recordSummary record).cheap * Real.log (p.repair.scale.width.cheapCharge : ℝ) +
      (recordSummary record).cuts * Real.log (p.repair.scale.width.cutCharge : ℝ) +
      ((recordHubs record).map (hubPrice exponent)).sum +
      ((recordHubs record).filter (fun tagged => tagged.2.scale)).length *
        Real.log (2 * (4 : ℝ) ^ p.repair.scale.width.B) := by
  simpa only [recordHubs, List.map_map, Function.comp_def, hubPrice,
    List.filter_map, List.length_map, scaleCount] using
      (recordSummary record).priced_separated (exponent record.identity) cap

theorem records_priced (records : List (RepairRecord p n)) (exponent : ℕ → ℕ)
    (cap : ∀ record ∈ records, record.result.final.pool.palette + 1 ≤ 2 ^ exponent record.identity) :
    (records.map (fun record => logCharge record.result.trace)).sum ≤
      ((records.map (fun record => (recordSummary record).cheap)).sum : ℝ) *
          Real.log (p.repair.scale.width.cheapCharge : ℝ) +
      ((records.map (fun record => (recordSummary record).cuts)).sum : ℝ) *
          Real.log (p.repair.scale.width.cutCharge : ℝ) +
      ((records.flatMap recordHubs).map (hubPrice exponent)).sum +
      ((records.flatMap recordHubs).filter (fun tagged => tagged.2.scale)).length *
        Real.log (2 * (4 : ℝ) ^ p.repair.scale.width.B) := by
  induction records with
  | nil => simp
  | cons record rest ih =>
    have hh := record_priced record exponent (cap record (List.mem_cons_self ..))
    have ht := ih (fun r hr => cap r (List.mem_cons_of_mem _ hr))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
      List.filter_append, List.length_append, Nat.cast_add, add_mul]
    linarith

/-- The only capacity premise concerns concrete final palettes. It is
supplied by the final stored-node index and transported historical births. -/
theorem run_priced (s : Active p n) (history : History n) (exponent : ℕ → ℕ)
    (cap : ∀ record ∈ runRecords s history,
      record.result.final.pool.palette + 1 ≤ 2 ^ exponent record.identity) :
    runDebit s history ≤
      runCheap s history * Real.log (p.repair.scale.width.cheapCharge : ℝ) +
      runCuts s history * Real.log (p.repair.scale.width.cutCharge : ℝ) +
      ((runHubs s history).map (hubPrice exponent)).sum +
      runScale s history * Real.log (2 * (4 : ℝ) ^ p.repair.scale.width.B) :=
  records_priced (runRecords s history) exponent cap

end SortingAdversary.Optimal.ControllerPricing
