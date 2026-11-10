import SortingAdversary.Continuous.ControllerConsequences

/-!
# Uniform consequences with the inactive parameter branch

The bounded parameter selector may return a value below 64 on small inputs.
The actual machine then uses the fixed identity ranking. Only eventual
qualification is needed for the asymptotic comparison theorem. For target
production the finitely many unqualified sizes have error exactly one, as in
the manuscript.
-/

namespace SortingAdversary.Continuous.Controller

open Filter
open scoped Topology

variable {n : ℕ}

theorem consistent_small {k : ℕ} (hk : k < 64) (t : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (t.run (strategy k) []).observations := by
  have hs : Sound (fun _ : Memory n => False) (replay k []) [] := by
    change Sound (fun _ : Memory n => False) (start n k) []
    simp only [start, if_neg (not_le.mpr hk), Sound]
    exact ⟨Equiv.refl _, rfl, compatible_nil _⟩
  obtain ⟨π, _, hπ⟩ := run_consistent_of_memory_invariant (fun _ : Memory n => False) k
    (fun M hM => hM.elim) t [] hs
  exact ⟨π, hπ⟩

theorem consistent_parameter_schedule (stage : ℕ → ℕ)
    (hcompare : ∀ n, 64 ≤ stage n → CompareGuarantee n (stage n)) :
    SortingAdversary.Optimal.ConsistentFamily (fun n => strategy (stage n)) := by
  intro n t
  by_cases hk : 64 ≤ stage n
  · exact consistent_of_compare_guarantee hk (hcompare n hk) t
  · exact consistent_small (lt_of_not_ge hk) t

/-- The parameter need only eventually enter the active range. This theorem
applies directly to the bounded stage selector, including its inactive
sentinel on the remaining inputs. -/
theorem asymptoticallyOptimal_of_eventual_compare_guarantee (stage : ℕ → ℕ)
    (hstage : Tendsto stage atTop atTop)
    (hcompare : ∀ n, 64 ≤ stage n → CompareGuarantee n (stage n)) :
    SortingAdversary.Optimal.AsymptoticallyOptimal (fun n => strategy (stage n)) := by
  refine ⟨consistent_parameter_schedule stage hcompare, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hqual : ∀ᶠ n in atTop, 64 ≤ stage n := (tendsto_atTop.1 hstage) 64
  have hδ : ∀ᶠ n in atTop, prefixOverhead (stage n) < ε / 2 :=
    (tendsto_order.1 (selected_overhead_tendsto stage hstage)).2 _ hhalf
  have hrem : ∀ᶠ n : ℕ in atTop, (n / Real.log 2) / nLog2n n < ε / 2 :=
    (tendsto_order.1 linear_remainder_tendsto).2 _ hhalf
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hqual.and (hδ.and hrem))
  refine ⟨max 2 N, ?_⟩
  intro n hn t ht
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hk, hδn, hremn⟩ := hN n hnN
  have hT := SortingAdversary.Optimal.nLog2n_positive hn2
  have hb := sorting_bound_of_prefix (strategy (stage n)) t ht (prefixOverhead (stage n))
    (consistent_of_compare_guarantee hk (hcompare n hk) t)
    (prefix_of_compare_guarantee hk (hcompare n hk))
  have hf := log_factorial_lower n
  have hbudget : nLog2n n ≤ (1 + prefixOverhead (stage n)) *
      (t.run (strategy (stage n)) []).comparisons + n / Real.log 2 := by linarith
  apply SortingAdversary.Optimal.relative_clock_bound hT.le (Nat.cast_nonneg _) hε.le
    hbudget hδn.le
  exact (div_le_iff₀ hT).mp hremn.le

noncomputable def stageError (stage : ℕ → ℕ) (n : ℕ) : ℝ :=
  if 64 ≤ stage n then productionError (stage n) else 1

theorem stageError_nonneg (stage : ℕ → ℕ) (n : ℕ) : 0 ≤ stageError stage n := by
  unfold stageError
  split
  · rename_i hk
    exact (productionError_bounds (by exact_mod_cast hk)).1
  · norm_num

theorem stageError_tendsto (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop) :
    Tendsto (stageError stage) atTop (𝓝 0) := by
  apply (selected_productionError_tendsto stage hstage).congr'
  filter_upwards [(tendsto_atTop.1 hstage) 64] with n hn
  simp only [stageError, if_pos hn]

/-- One nonnegative error sequence works uniformly for every target, with
the exact inactive-branch convention in the paper. -/
theorem production_parameter_schedule (stage : ℕ → ℕ)
    (hcompare : ∀ n, 64 ≤ stage n → CompareGuarantee n (stage n))
    (n : ℕ) (h : History n) (hf : Follows (strategy (stage n)) h)
    (R : Item n → Item n → Prop) (assignment : Ranking n)
    (hcorrect : ∀ π, Compatible π h → Produces R assignment π) :
    (1 - stageError stage n) * (log2 (n.factorial : ℝ) - log2 (extensionCount R : ℝ)) ≤
      h.length := by
  unfold stageError
  split
  · rename_i hk
    exact production_of_compare_guarantee hk (hcompare n hk) h hf R assignment hcorrect
  · simp

end SortingAdversary.Continuous.Controller
