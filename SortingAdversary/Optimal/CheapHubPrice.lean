import SortingAdversary.Optimal.RepairSignedPrice

/-!
# One daughter factorial pays cheap and expensive admissions together

The full receiving population is split into cheap admissions and all hub
admissions. Factorial supermultiplicativity leaves the exact expensive
factorial credit intact and costs at most one cheap scalar per daughter.
-/

namespace SortingAdversary.Optimal.CheapHubPrice

open scoped BigOperators

theorem log_factorial_split (population hubs : ℕ) (h : hubs ≤ population) :
    Real.log ((population - hubs).factorial : ℝ) + Real.log (hubs.factorial : ℝ) ≤
      Real.log (population.factorial : ℝ) := by
  have hn : (population - hubs).factorial * hubs.factorial ≤ population.factorial := by
    have hd := Nat.factorial_mul_factorial_dvd_factorial_add (population - hubs) hubs
    rw [Nat.sub_add_cancel h] at hd
    exact Nat.le_of_dvd (Nat.factorial_pos _) hd
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  exact_mod_cast hn

/-- The bound is independent of the number of cheap admissions to a
daughter. The expensive credit is subtracted before any price truncation. -/
theorem split_debit {ι : Type*} (destinations : Finset ι) (population hubs : ι → ℕ)
    (bounded : ∀ c ∈ destinations, hubs c ≤ population c)
    (A debit : ℝ) (positive : 0 < A) :
    ((∑ c ∈ destinations, (population c - hubs c : ℕ)) : ℝ) * Real.log A + debit -
        (∑ c ∈ destinations, Real.log ((population c).factorial : ℝ)) ≤
      (destinations.card : ℝ) * A +
        (debit - ∑ c ∈ destinations, Real.log ((hubs c).factorial : ℝ)) := by
  have hs := Finset.sum_le_sum (fun c hc => log_factorial_split (population c) (hubs c) (bounded c hc))
  have hc := Accounting.sum_cheap_signed_debit_le destinations (fun c => population c - hubs c) A positive
  simp only [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Nat.cast_sum] at hc ⊢
  linarith

theorem split_debit_of_mass {ι : Type*} (destinations : Finset ι) (population hubs : ι → ℕ)
    (bounded : ∀ c ∈ destinations, hubs c ≤ population c) (cheap : ℕ)
    (mass : cheap + ∑ c ∈ destinations, hubs c = ∑ c ∈ destinations, population c)
    (A debit : ℝ) (positive : 0 < A) :
    (cheap : ℝ) * Real.log A + debit -
        (∑ c ∈ destinations, Real.log ((population c).factorial : ℝ)) ≤
      (destinations.card : ℝ) * A +
        (debit - ∑ c ∈ destinations, Real.log ((hubs c).factorial : ℝ)) := by
  have he : cheap = ∑ c ∈ destinations, (population c - hubs c) := by
    have hh : (∑ c ∈ destinations, (population c - hubs c)) + ∑ c ∈ destinations, hubs c =
        ∑ c ∈ destinations, population c := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c hc => Nat.sub_add_cancel (bounded c hc))
    omega
  rw [he]
  simpa only [Nat.cast_sum] using split_debit destinations population hubs bounded A debit positive

end SortingAdversary.Optimal.CheapHubPrice
