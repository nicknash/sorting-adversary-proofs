import SortingAdversary.Optimal.UniformRates

/-!
# Final scalar reduction for the actual uniform family

The finite budget is expressed in natural logarithms. The coefficient and
remainder below use the concrete selected stage. The execution accounting
instantiates the remaining finite inequality; the cutoff branch is handled
directly by the actual implemented clock.
-/

namespace SortingAdversary.Optimal.UniformAdversary

open Filter AsymptoticRates SignedPrice
open scoped Topology

theorem natural_budget_to_comparisons (n : ℕ) (hn : 2 ≤ n)
    (hj : 0 < UniformStage.selectedStage n) (q X budget : ℝ)
    (hq : 0 ≤ q) (hX : 0 ≤ X) (hbudget : 0 ≤ budget)
    (hXcap : X ≤ (12 / (UniformStage.selectedStage n : ℝ)) * ((n : ℝ) * Real.log n))
    (hcap : budget ≤ 256 * ((n : ℝ) * Real.log n))
    (haccount : (n : ℝ) * Real.log n ≤
      q * (-Real.log (1 / 2 - stageTolerance (UniformStage.selectedStage n)) -
        Real.log (1 - stageTolerance (UniformStage.selectedStage n))) +
      ((n : ℝ) * Real.log n) * terminalFraction n + 2 * n * selectedCheap n +
      ((n : ℝ) * Real.log n) / UniformStage.selectedStage n +
      priceCoefficient (Real.exp 1 * 128) * entropyEnvelope X budget) :
    nLog2n n ≤ (1 + overhead n) * q + nLog2n n * remainderFraction n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT := mul_pos hnpos hnlog
  have hA : 1 ≤ Real.exp 1 * (128 : ℝ) := by
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith
  have hprice := mul_le_mul_of_nonneg_left
    (envelope_scaled_le hT hj hX hbudget hXcap hcap) (priceCoefficient_nonneg hA)
  have htol := stageTolerance_bounds hj
  have hphysical := (div_le_iff₀ hlogtwo).mp
    (physical_and_cut_relative_le _ htol.1 htol.2)
  have hqprice := mul_le_mul_of_nonneg_left hphysical hq
  have hrem : ((n : ℝ) * Real.log n) * remainderFraction n =
      ((n : ℝ) * Real.log n) * terminalFraction n + 2 * n * selectedCheap n +
      ((n : ℝ) * Real.log n) / UniformStage.selectedStage n +
      priceCoefficient (Real.exp 1 * 128) *
        (((n : ℝ) * Real.log n) * entropyEnvelope
          (12 / (UniformStage.selectedStage n : ℝ)) 256) := by
    unfold remainderFraction
    field_simp
    <;> ring
  have hmain : (n : ℝ) * Real.log n ≤
      (1 + overhead n) * q * Real.log 2 + ((n : ℝ) * Real.log n) * remainderFraction n := by
    rw [hrem]
    unfold overhead
    nlinarith
  apply (mul_le_mul_iff_left₀ hlogtwo).mp
  have hnEq : Real.log 2 * nLog2n n = (n : ℝ) * Real.log n := by
    unfold nLog2n
    field_simp
  rw [add_mul]
  nlinarith [congrArg (fun z : ℝ => z * remainderFraction n) hnEq]

/-- Only the actual active-run budget remains as a premise here. Legality,
the fallback-to-controller transition, the cutoff, and both vanishing rates
are supplied by the constructed uniform family itself. -/
theorem optimal_of_active_accounting
    (hbudget : ∀ᶠ n : ℕ in atTop, 2 ≤ n →
      ∀ t : DecisionTree n, t.Correct →
        (t.run (strategy n) []).comparisons ≤ cutoff n →
          nLog2n n ≤ (1 + overhead n) * ((t.run (strategy n) []).comparisons : ℝ) +
            nLog2n n * remainderFraction n) :
    AsymptoticallyOptimal strategy := by
  refine ⟨consistent, ?_⟩
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  have he : ∀ᶠ n : ℕ in atTop,
      (2 ≤ n ∧ overhead n < δ / 2) ∧ remainderFraction n < δ / 2 ∧
      (2 ≤ n → ∀ t : DecisionTree n, t.Correct →
        (t.run (strategy n) []).comparisons ≤ cutoff n →
          nLog2n n ≤ (1 + overhead n) * ((t.run (strategy n) []).comparisons : ℝ) +
            nLog2n n * remainderFraction n) :=
    ((eventually_ge_atTop 2).and ((tendsto_order.mp overhead_tendsto).2 _ hhalf)).and
      (((tendsto_order.mp remainderFraction_tendsto).2 _ hhalf).and hbudget)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro n hn t ht
  obtain ⟨⟨hn2, hover⟩, hrem, hbudget⟩ := hN n hn
  have hT := (nLog2n_positive hn2).le
  by_cases hc : (t.run (strategy n) []).comparisons ≤ cutoff n
  · apply relative_clock_bound hT (Nat.cast_nonneg _) hδ.le (hbudget hn2 t ht hc) hover.le
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hrem.le hT
  · have hcut := nLog2n_le_cutoff hn2
    have hclock : (cutoff n : ℝ) ≤ (t.run (strategy n) []).comparisons := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    have hδT : 0 ≤ δ * nLog2n n := mul_nonneg hδ.le hT
    nlinarith

end SortingAdversary.Optimal.UniformAdversary
