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

/-!
# Sorting-adversary formalization

This is the trusted, placeholder-free library root.  Its exported lower bound
is proved by the deterministic curvature/volumetric adversary. The recursive
colour construction has checked components under `SortingAdversary.Optimal`;
its complete polynomial-time leading-one theorem is not yet formalized.
-/
