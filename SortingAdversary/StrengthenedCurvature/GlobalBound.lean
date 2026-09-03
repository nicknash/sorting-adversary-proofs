import SortingAdversary.StrengthenedCurvature.AdversaryPotential
import SortingAdversary.StrengthenedCurvature.SourceSpecification
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# From the one-comparison theorem to the asymptotic constant

This module performs the global telescoping and the exact algebra which turns
the determinant ratio `7361 / 1000` into the leading coefficient
`2 / log₂ (7361 / 1000)`.  The remaining geometric development has one explicit
interface to instantiate: `CertifiedRuleFamily`.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- Half the base-two logarithm of the certified determinant ratio. -/
noncomputable def comparisonBudget : ℝ :=
  Real.log strengthenedDeterminantRatio / (2 * Real.log 2)

/-- A sufficient terminal endpoint once the transcript determines the order.

The paper records the sharper `(n+1/2) log₂(n+1)` bound using all `n+1`
grounded-path rows.  For the leading constant we use the simpler `n log₂ n`
minor consisting of the lower boundary row and the `n-1` adjacent comparison
rows.  Its incidence matrix is triangular with determinant one. -/
noncomputable def terminalPotentialLower (n : ℕ) : ℝ :=
  nLog2n n

theorem strengthenedDeterminantRatio_eq :
    strengthenedDeterminantRatio = (7361 : ℝ) / 1000 := rfl

theorem one_lt_strengthenedDeterminantRatio :
    (1 : ℝ) < strengthenedDeterminantRatio := by
  norm_num [strengthenedDeterminantRatio]

theorem comparisonBudget_pos : 0 < comparisonBudget := by
  have hratio : 0 < Real.log strengthenedDeterminantRatio :=
    Real.log_pos one_lt_strengthenedDeterminantRatio
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact div_pos hratio (mul_pos (by norm_num) htwo)

theorem strengthenedCurvatureConstant_eq_invBudget :
    strengthenedCurvatureConstant = comparisonBudget⁻¹ := by
  have hlogtwo : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogratio : Real.log strengthenedDeterminantRatio ≠ 0 :=
    ne_of_gt (Real.log_pos one_lt_strengthenedDeterminantRatio)
  rw [strengthenedCurvatureConstant, comparisonBudget]
  field_simp

/-- The exact analytic obligations supplied by the local geometric proof.

For each input size this contains one history-dependent potential rule.  Its
initial value is at most `3n/2`; every local increase is at most half the
base-two logarithm of `7361/1000`; and correctness forces the terminal path
potential to reach the path-determinant endpoint.
-/
structure CertifiedRuleFamily where
  rule : ∀ n : ℕ, PotentialRule n
  maxIncrease_eq : ∀ n : ℕ, (rule n).maxIncrease = comparisonBudget
  initial_upper : ∀ n : ℕ, (rule n).potential [] ≤ (3 / 2 : ℝ) * n
  terminal_lower : ∀ (n : ℕ) (t : DecisionTree n), t.Correct →
    ∀ π : Ranking n,
      Compatible π (t.run (rule n).strategy []).observations →
      terminalPotentialLower n ≤
        (rule n).potential (t.run (rule n).strategy []).observations.reverse

namespace CertifiedRuleFamily

/-- The strategies certified by a geometric rule family. -/
noncomputable def strategies (cert : CertifiedRuleFamily) : ∀ n : ℕ, Strategy n :=
  fun n => (cert.rule n).strategy

/-- Exact per-tree comparison bound before the asymptotic simplification. -/
theorem exact_run_bound (cert : CertifiedRuleFamily) (n : ℕ)
    (t : DecisionTree n) (ht : t.Correct) :
    terminalPotentialLower n - (3 / 2 : ℝ) * n ≤
      (t.run (cert.rule n).strategy []).comparisons * comparisonBudget := by
  have hglobal := (cert.rule n).comparisons_lower_bound t (terminalPotentialLower n)
    (cert.terminal_lower n t ht)
  rw [cert.maxIncrease_eq n] at hglobal
  exact (sub_le_sub_left (cert.initial_upper n) _).trans hglobal

/-- A certified rule family proves the online, history-dependent adversary
statement with the exact source constant. -/
theorem target (cert : CertifiedRuleFamily) : StrengthenedCurvatureTarget := by
  refine ⟨cert.strategies, (3 / 2 : ℝ) / comparisonBudget,
    (div_nonneg (by norm_num) comparisonBudget_pos.le), ?_⟩
  intro n hn t ht
  have hrun := cert.exact_run_bound n t ht
  have hquot :
      (terminalPotentialLower n - (3 / 2 : ℝ) * n) / comparisonBudget ≤
        ((t.run (cert.rule n).strategy []).comparisons : ℝ) := by
    apply (div_le_iff₀ comparisonBudget_pos).2
    simpa [mul_comm] using hrun
  constructor
  · simpa [strategies] using (cert.rule n).run_consistent t
  · rw [strengthenedCurvatureConstant_eq_invBudget]
    calc
      comparisonBudget⁻¹ * nLog2n n -
          ((3 / 2 : ℝ) / comparisonBudget) * n =
          (nLog2n n - (3 / 2 : ℝ) * n) / comparisonBudget := by
            field_simp [ne_of_gt comparisonBudget_pos]
      _ = (terminalPotentialLower n - (3 / 2 : ℝ) * n) / comparisonBudget := rfl
      _ ≤ ((t.run (cert.rule n).strategy []).comparisons : ℝ) := hquot

end CertifiedRuleFamily
end StrengthenedCurvature
end SortingAdversary
