import SortingAdversary.Strategy
import SortingAdversary.AsymptoticStatement
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The precise comparison guarantee and its accounting reduction

This file states the online leading-one target using the repository's actual
sorting-tree semantics. It proves the final reduction from a vanishing-error
accounting inequality. The accounting inequality and consistency remain
explicit hypotheses in this general reduction. `UniformOptimal` instantiates
them for the constructed recursive controller. Polynomial running time is a
separate assertion.
-/

namespace SortingAdversary.Optimal

open Filter

/-- A single family of deterministic transcript-dependent strategies is legal
against every finite comparison tree, including incorrect trees. -/
def ConsistentFamily (strategy : ∀ n, Strategy n) : Prop :=
  ∀ n (t : DecisionTree n),
    ∃ π : Ranking n, Compatible π (t.run (strategy n) []).observations

/-- The leading-one *online comparison* guarantee. This does not express
computability or polynomial time; these are separate obligations. -/
def AsymptoticallyOptimal (strategy : ∀ n, Strategy n) : Prop :=
  ConsistentFamily strategy ∧
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : DecisionTree n, t.Correct →
        (1 - δ) * nLog2n n ≤ ((t.run (strategy n) []).comparisons : ℝ)

theorem nLog2n_positive {n : ℕ} (hn : 2 ≤ n) : 0 < nLog2n n := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  unfold nLog2n
  exact mul_pos (lt_trans zero_lt_one hnreal)
    (div_pos (Real.log_pos hnreal) (Real.log_pos (by norm_num)))

/-- The elementary final inequality, with no hidden asymptotic constants.
Both the per-comparison overhead and the residual debit may be negative;
only their stated upper bounds are needed. -/
theorem relative_clock_bound {T q overhead remainder δ : ℝ}
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hbudget : T ≤ (1 + overhead) * q + remainder)
    (hoverhead : overhead ≤ δ / 2)
    (hremainder : remainder ≤ (δ / 2) * T) : (1 - δ) * T ≤ q := by
  have hscaled : T ≤ (1 + δ / 2) * q + (δ / 2) * T := by
    calc
      T ≤ (1 + overhead) * q + remainder := hbudget
      _ ≤ (1 + δ / 2) * q + (δ / 2) * T :=
        add_le_add (mul_le_mul_of_nonneg_right (by linarith) hq) hremainder
  have hquadratic : 0 ≤ δ * δ * T := mul_nonneg (mul_self_nonneg δ) hT
  have hfactor : 0 < 1 + δ / 2 := by linarith
  apply (mul_le_mul_iff_right₀ hfactor).mp
  nlinarith

/-- A fully proved semantic reduction: a legal strategy whose exact accounting
has vanishing relative error has the stated online comparison guarantee.

This theorem is deliberately conditional. `UniformOptimal` proves the
unconditional comparison guarantee for the actual recursive colour controller;
the controller's running time has a separate cost model.
-/
theorem comparison_guarantee_of_vanishing_accounting
    (strategy : ∀ n, Strategy n) (overhead remainder : ℕ → ℝ)
    (hconsistent : ConsistentFamily strategy)
    (hbudget : ∀ n : ℕ, 2 ≤ n → ∀ t : DecisionTree n, t.Correct →
      nLog2n n ≤ (1 + overhead n) *
        ((t.run (strategy n) []).comparisons : ℝ) + remainder n)
    (hoverhead : Tendsto overhead atTop (nhds 0))
    (hremainder : Tendsto (fun n => remainder n / nLog2n n) atTop (nhds 0)) :
    AsymptoticallyOptimal strategy := by
  refine ⟨hconsistent, ?_⟩
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  have hevent : ∀ᶠ n in atTop,
      overhead n < δ / 2 ∧ remainder n / nLog2n n < δ / 2 :=
    ((tendsto_order.1 hoverhead).2 _ hhalf).and
      ((tendsto_order.1 hremainder).2 _ hhalf)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 2 N, ?_⟩
  intro n hn t ht
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hpos := nLog2n_positive hn2
  have herr := hN n hnN
  apply relative_clock_bound hpos.le (Nat.cast_nonneg _) hδ.le
    (hbudget n hn2 t ht) herr.1.le
  exact (div_le_iff₀ hpos).mp herr.2.le

/-- The same online bound holds on a genuine input of every correct sorter.
This uses the existing transcript-to-ranking semantic bridge. -/
theorem asymptotic_worst_case (strategy : ∀ n, Strategy n)
    (h : AsymptoticallyOptimal strategy) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : DecisionTree n, t.Correct →
        ∃ π : Ranking n, (1 - δ) * nLog2n n ≤ (t.cost π : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := h.2 δ hδ
  refine ⟨N, ?_⟩
  intro n hn t ht
  obtain ⟨π, hπ⟩ := h.1 n t
  refine ⟨π, ?_⟩
  rw [(t.run_matches_compatible_ranking (strategy n) [] π hπ).2]
  exact hN n hn t ht

end SortingAdversary.Optimal
