import SortingAdversary.StrengthenedCurvature.EfficientOneComparison
import SortingAdversary.StrengthenedCurvature.Endpoints
import SortingAdversary.StrengthenedCurvature.GlobalBound

/-!
# The efficient deterministic curvature adversary

This file closes the global proof.  `efficientInformativeRule` is the local
volumetric rule from the notes.  `toPotentialRule` answers repeated and
transitively implied queries for free, while retaining only informative rows.
The endpoint determinant estimate then converts the local `347 / 50`
determinant ratio into the final comparison lower bound.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

theorem strengthenedComparisonBudget_eq_comparisonBudget :
    strengthenedComparisonBudget = comparisonBudget := by
  simp [strengthenedComparisonBudget, comparisonBudget, strengthenedK,
    strengthenedDeterminantRatio]

/-- The geometric rule, together with its initial and terminal potential
estimates, packaged for the global telescoping theorem. -/
noncomputable def efficientCertifiedRuleFamily : CertifiedRuleFamily where
  rule := efficientPotentialRule
  maxIncrease_eq := by
    intro n
    exact strengthenedComparisonBudget_eq_comparisonBudget
  initial_upper := by
    intro n
    simpa [efficientPotentialRule, InformativePotentialRule.toPotentialRule,
      InformativePotentialRule.rawPotential, efficientInformativeRule,
      retainedHistory] using
      (historyPotential_nil_upper (n := n))
  terminal_lower := by
    intro n t ht π hπ
    change terminalPotentialLower n ≤
      historyPotential (retainedHistory
        (t.run (efficientPotentialRule n).strategy []).observations.reverse)
    exact retained_terminal_potential_lower t (efficientPotentialRule n).strategy ht π hπ

/-- The source-backed online adversary theorem.  Its leading coefficient is
`2 / log₂(347/50)`, approximately `0.7155799779`. -/
theorem efficient_curvature_adversary : StrengthenedCurvatureTarget :=
  efficientCertifiedRuleFamily.target

end StrengthenedCurvature
end SortingAdversary
