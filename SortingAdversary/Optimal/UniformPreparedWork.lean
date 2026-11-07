import SortingAdversary.Optimal.UniformRepairWork

/-! Both admitted-stage oracle radii are computed once and stored. -/

namespace SortingAdversary.Optimal.UniformPreparedWork

open PrimitiveWork UniformStage

variable {n j : ℕ}

structure Data (a : Accepted (Parameters.logCap n) j) where
  repair : UniformRepairWork.Prepared a
  comparisonRadius : ℕ
  comparison_exact : comparisonRadius = a.runtime.normalizer.scale.H *
    LocalParameters.sweepCount a.runtime.normalizer.scale.H
      (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d)
      a.runtime.normalizer.scale.R a.runtime.ε

def prepare (a : Accepted (Parameters.logCap n) j) : Result (Data a) :=
  let repair := UniformRepairWork.prepare a
  let comparison := UniformScalarWork.comparison a
  ⟨⟨repair.value, comparison.value, UniformScalarWork.comparison_value a⟩,
    repair.work + comparison.work + 2⟩

theorem work_le_cap (a : Accepted (Parameters.logCap n) j) :
    (prepare a).work ≤ 28 * Parameters.logCap n + 82 := by
  have hr := UniformRepairWork.prepare_work a
  have hc := UniformScalarWork.comparison_work a
  change (UniformRepairWork.prepare a).work + (UniformScalarWork.comparison a).work + 2 ≤ _
  omega

theorem work_le (a : Accepted (Parameters.logCap n) j) :
    (prepare a).work ≤ 28 * (n + 1) + 82 := by
  have h := work_le_cap a
  have hl : Parameters.logCap n ≤ n + 1 := Nat.log_le_self 2 (n + 1)
  omega

theorem radii_le_cap (a : Accepted (Parameters.logCap n) j) :
    (prepare a).value.repair.radius ≤ Parameters.logCap n ∧
      (prepare a).value.comparisonRadius ≤ Parameters.logCap n :=
  ⟨UniformRepairWork.prepare_radius a, UniformScalarWork.comparison_cap a⟩

end SortingAdversary.Optimal.UniformPreparedWork
