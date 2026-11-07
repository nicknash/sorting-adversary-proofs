import SortingAdversary.Optimal.RepresentationTrace
import SortingAdversary.Optimal.OrdinaryPromotion

/-!
# The measured ordinary-promotion interface

The result contains the actual executable ordinary move and its cached
getters. Equality to the reference routine and the getter bound are erased
proofs, rather than inputs supplying a claimed computation cost.
-/

namespace SortingAdversary.Optimal.MeasuredOrdinaryPromotion

open WidthRepair RepresentationWork LocalOracle SeparatedPins

variable {n : ℕ}

structure Output (s : State n) (H d : ℕ) (g : SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v) where
  result : OrdinaryPromotion.Move s
  access : LocalAccess result.update.next
  actual : result = OrdinaryPromotion.make s H d g R hR v hmark hv hm
  cached : AccessBound access 2

abbrev Executor (n H d : ℕ) (R : ℚ) :=
  {s : State n} → (access : LocalAccess s) → AccessBound access 2 →
    (g : SparseBounds s.rows H d) → (hR : 0 ≤ R) →
    (v : Fin n) → (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v) →
    (hv : s.pool.pins v = none) → (hm : HasMate s.pool v) →
    PrimitiveWork.Result (Output s H d g R hR v hmark hv hm)

end SortingAdversary.Optimal.MeasuredOrdinaryPromotion
