import SortingAdversary.DecisionTree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Human-readable asymptotic target

This file fixes the intended meaning of a leading constant.  It is a
specification, not a proof of the 0.72 result.
-/

namespace SortingAdversary

/-- The real-valued quantity `n log₂ n`. -/
noncomputable def nLog2n (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log n / Real.log 2)

/-- Every correct deterministic comparison tree has an input requiring
`c n log₂ n - O(n)` comparisons, with one uniform linear-error constant. -/
def HasLeadingConstant (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ t : DecisionTree n, t.Correct →
    ∃ π : Ranking n,
      c * nLog2n n - C * n ≤ (t.cost π : ℝ)

/-- The clean rational theorem requested for the strongest adversary. -/
def Target072 : Prop := HasLeadingConstant (18 / 25 : ℝ)

end SortingAdversary
