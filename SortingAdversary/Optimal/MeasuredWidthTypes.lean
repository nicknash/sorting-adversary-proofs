import SortingAdversary.Optimal.RepresentationTrace
import SortingAdversary.Optimal.WidthScale

/-!
# Result interfaces for measured width execution

The executable data is the actual certified width result together with its
cached getters. The reference equality is proof-only and does not evaluate
the reference executor.
-/

namespace SortingAdversary.Optimal.MeasuredWidthNormalize

open WidthRepair RepresentationWork LocalOracle

variable {n : ℕ}

structure Output (s : State n) (p : ScaleParameters) (d : ℕ)
    (g : SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B) where
  result : WidthResult s p
  access : LocalAccess result.final
  actual : result = WidthRepair.normalizeWidths s p d g hB
  cached : AccessBound access 2

abbrev Executor (n : ℕ) :=
  {s : State n} → (access : LocalAccess s) → AccessBound access 2 →
    (p : ScaleParameters) → (d : ℕ) → (g : SparseBounds s.rows p.H d) →
    (hB : ComparableBound s p.width.B) → PrimitiveWork.Result (Output s p d g hB)

end SortingAdversary.Optimal.MeasuredWidthNormalize

namespace SortingAdversary.Optimal.MeasuredEarlyNormalize

open WidthRepair RepresentationWork

variable {n : ℕ}

structure Output (s : State n) (p : WidthParameters) (hB : ComparableBound s p.B) where
  result : EarlyResult s p
  access : LocalAccess result.final
  actual : result = WidthRepair.normalizeEarly s p hB
  cached : AccessBound access 2

end SortingAdversary.Optimal.MeasuredEarlyNormalize

