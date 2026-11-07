import SortingAdversary.Optimal.UniformExecution
import SortingAdversary.Optimal.UniformRunBudgets
import SortingAdversary.Optimal.ControllerPriceBudget
import SortingAdversary.Optimal.UniformComparisonReduction
import SortingAdversary.Optimal.CutRun

/-!
# The constructed uniform adversary is asymptotically optimal

Every finite accounting input below is extracted from the actual controller
execution. The bounded stage selector, physical cutoff, cheap admissions,
common expensive dictionary, scale surcharge, and terminal tree estimate
together give the leading-one online comparison bound. In particular, the
main theorem has no oracle, ledger, pricing, or asymptotic hypotheses.
-/

namespace SortingAdversary.Optimal.UniformAdversary

open Filter AsymptoticRates ControllerMachine ControllerRun ControllerPricing

theorem accepted_physicalPrice {cap j : ℕ} (a : UniformStage.Accepted cap j) :
    LedgerControllerPrices.physicalPrice a.controller =
      -Real.log (1 / 2 - stageTolerance j) := by
  unfold LedgerControllerPrices.physicalPrice
  have he : a.controller.error = 1 / (100 * (j : ℚ)) := a.accuracy
  rw [he]
  simp only [Rat.cast_inv, Rat.cast_sub, Rat.cast_ofNat,
    Rat.cast_mul, Rat.cast_natCast, one_div, Real.log_inv, stageTolerance]

/-- The actual active execution supplies the complete finite inequality.
Only the selected package and the numerical physical-clock bound are used. -/
theorem selected_comparison_budget {N j : ℕ} {hj : 0 < j}
    (a : UniformStage.Accepted (Parameters.logCap (N + 2)) j)
    (he : (UniformStage.choose (N + 2)).decision = .accepted j hj a)
    (t : DecisionTree (N + 2)) (ht : t.Correct)
    (hcutoff : (t.run (strategy (N + 2)) []).comparisons ≤ cutoff (N + 2))
    (hclock : (cutoff (N + 2) : ℝ) ≤
      4 * ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) :
    nLog2n (N + 2) ≤
      (1 + overhead (N + 2)) * ((t.run (strategy (N + 2)) []).comparisons : ℝ) +
      nLog2n (N + 2) * remainderFraction (N + 2) := by
  obtain ⟨final, run, total⟩ := selected_activeRun a he t ht hcutoff
  let observations := (t.run (strategy (N + 2)) []).observations
  have hlength : observations.length = (t.run (strategy (N + 2)) []).comparisons :=
    t.run_observations_length (strategy (N + 2)) []
  have hq : (observations.length : ℝ) ≤ 4 * UniformRunBudgets.entropy N := by
    have hc : (observations.length : ℝ) ≤ cutoff (N + 2) := by
      exact_mod_cast (show observations.length ≤ cutoff (N + 2) by rw [hlength]; exact hcutoff)
    unfold UniformRunBudgets.entropy
    nlinarith
  have hstage := selectedStage_eq a he
  have hpositive : 0 < UniformStage.selectedStage (N + 2) := by rw [hstage]; exact hj
  let hubs := runHubs (initialActive a.controller N) observations
  let budget := ControllerFinalPrice.hubBudget final.tree hubs
  have hbudget : 0 ≤ budget ∧ budget ≤ 256 * UniformRunBudgets.entropy N :=
    ControllerFinalPrice.actual_budget_bounds a.controller N run hq
  have hmass : (hubs.length : ℝ) ≤ (12 / (j : ℝ)) * UniformRunBudgets.entropy N :=
    UniformRunBudgets.actual_hub_mass_le a hj N run hq
  have hterminal := active_terminal_bound a.controller N run total
    (by simpa only [UniformRunBudgets.entropy, mul_assoc] using hq)
  have hscale := UniformRunBudgets.actual_scale_surcharge_le a hj N run
  have hprice := ControllerFinalPrice.actual_price a.controller N run
  have hcuts : (runCuts (initialActive a.controller N) observations : ℝ) ≤ observations.length := by
    exact_mod_cast CutAccounting.initial_cuts_le a.controller N run
  have htol := stageTolerance_bounds hj
  have hcutnonneg : 0 ≤ -Real.log (1 - stageTolerance j) := by
    apply neg_nonneg.mpr
    exact Real.log_nonpos (by linarith) (by linarith)
  have hcutprice :
      (runCuts (initialActive a.controller N) observations : ℝ) *
          Real.log (a.controller.repair.scale.width.cutCharge : ℝ) ≤
      observations.length * (-Real.log (1 - stageTolerance j)) :=
    (mul_le_mul_of_nonneg_left (cut_log_le a hj) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcuts hcutnonneg)
  have hcheap : (selectedCheap (N + 2) : ℝ) =
      (a.controller.repair.scale.width.cheapCharge : ℝ) := by
    rw [selectedCheap_eq a he]
    exact cheap_cast_eq a
  have haccount : ((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) ≤
      (observations.length : ℝ) *
        (-Real.log (1 / 2 - stageTolerance j) - Real.log (1 - stageTolerance j)) +
      (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) * terminalFraction (N + 2) +
      2 * (N + 2 : ℕ) * (selectedCheap (N + 2) : ℝ) +
      (((N + 2 : ℕ) : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) / j +
      SignedPrice.priceCoefficient (Real.exp 1 * 128) *
        SignedPrice.entropyEnvelope hubs.length budget := by
    rw [accepted_physicalPrice a] at hprice
    rw [hcheap]
    change _ ≤ (observations.length : ℝ) * _ + _ + _ +
      SignedPrice.priceCoefficient (Real.exp 1 * 128) *
        SignedPrice.entropyEnvelope hubs.length budget + _ at hprice
    unfold UniformRunBudgets.entropy at hscale
    nlinarith
  have h := natural_budget_to_comparisons (N + 2) (by omega) hpositive
    observations.length hubs.length budget (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hbudget.1 (by simpa only [hstage, UniformRunBudgets.entropy] using hmass)
    hbudget.2 (by simpa only [hstage] using haccount)
  simpa only [hlength] using h

/-- The single executable uniform family is legal against every finite
comparison tree and forces `(1 - δ) n log₂ n` comparisons against every
correct sorter for all sufficiently large input sizes. -/
theorem asymptoticallyOptimal : AsymptoticallyOptimal strategy := by
  apply optimal_of_active_accounting
  filter_upwards [cutoff_eventually_le,
    UniformStage.selectedStage_tendsto.eventually (eventually_gt_atTop 0)] with n hclock hj
  intro hn t ht hcutoff
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  obtain ⟨a, he⟩ := selected_accepted (N + 2) hj
  exact selected_comparison_budget a he t ht hcutoff hclock

/-- The adversarial transcript is realized by a genuine ranking input of
every correct sorting tree. -/
theorem worst_case :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : DecisionTree n, t.Correct →
        ∃ π : Ranking n, (1 - δ) * nLog2n n ≤ (t.cost π : ℝ) :=
  asymptotic_worst_case strategy asymptoticallyOptimal

end SortingAdversary.Optimal.UniformAdversary
