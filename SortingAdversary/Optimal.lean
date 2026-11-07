import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.Routing
import SortingAdversary.Optimal.Refinement
import SortingAdversary.Optimal.FiniteRefinement
import SortingAdversary.Optimal.Insertion
import SortingAdversary.Optimal.LocalChoice
import SortingAdversary.Optimal.Terminal
import SortingAdversary.Optimal.Accounting
import SortingAdversary.Optimal.GroupEntropy
import SortingAdversary.Optimal.Endpoints
import SortingAdversary.Optimal.Parameters
import SortingAdversary.Optimal.ComparisonBound
import SortingAdversary.Optimal.Safety
import SortingAdversary.Optimal.ControllerRouting
import SortingAdversary.Optimal.PinTransitions
import SortingAdversary.Optimal.RefinementTransitions
import SortingAdversary.Optimal.FreshAdmission
import SortingAdversary.Optimal.SparseClosure
import SortingAdversary.Optimal.PublicOrder
import SortingAdversary.Optimal.PublicLegality
import SortingAdversary.Optimal.CompletedOrder
import SortingAdversary.Optimal.IdealCounting
import SortingAdversary.Optimal.DyadicDictionary
import SortingAdversary.Optimal.SignedPrice
import SortingAdversary.Optimal.Examples
import SortingAdversary.Optimal.Audit

/-!
# Checked components of the recursive colour sorting adversary

This root contains no admitted proof obligations. It does not yet construct the
complete polynomial-time adversary. See `docs/optimal-adversary-formalization.md`
for the precise coverage and outstanding mathematical and computational work.
The `Optimal.Audit` import rejects nonstandard axioms in this namespace.
-/
