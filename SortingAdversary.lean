import SortingAdversary.Basic
import SortingAdversary.DecisionTree
import SortingAdversary.Strategy
import SortingAdversary.Knowledge
import SortingAdversary.Potential
import SortingAdversary.PotentialAdversary
import SortingAdversary.AsymptoticStatement
import SortingAdversary.Examples.TwoItems
import SortingAdversary.StrengthenedCurvature.ApproximateRule
import SortingAdversary.StrengthenedCurvature.EfficientRule
import SortingAdversary.StrengthenedCurvature.Schedule
import SortingAdversary.Audit
import SortingAdversary.Optimal
import SortingAdversary.Continuous

/-!
# Sorting-adversary formalizations

The trusted library exports the current continuous construction under
`SortingAdversary.Continuous`, the earlier integer-colour construction under
`SortingAdversary.Optimal`, and the curvature/volumetric development.
Both leading-one constructions connect their actual online strategy to the
shared comparison-tree semantics. Their separate all-declaration axiom
audits allow only the standard logical axioms.
-/
