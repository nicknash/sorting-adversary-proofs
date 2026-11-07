import SortingAdversary.Optimal.RepairSelectWork
import SortingAdversary.Optimal.WidthScalarWork

/-! The scale-pair scan is driven by an explicitly computed ratio; the
semantic expression `p.R` occurs only in correctness certificates. -/

namespace SortingAdversary.Optimal.MeasuredScaleDecision

open PrimitiveWork RepresentationWork WidthRepair

variable {n : ℕ} {s : State n}

def select (a : LocalAccess s) (p : ScaleParameters) : Result (Option (ScaleTrigger s p)) :=
  let ratio := WidthScalarWork.ratio p
  let chosen := RepairSelectWork.scaleWitness a ratio.value
  match he : chosen.value with
  | none => ⟨none, ratio.work + chosen.work + 2⟩
  | some xy =>
    have hxy : WidthRepair.scaleWitness s p.R = some xy := by
      simpa only [chosen, RepairSelectWork.scaleWitness_value, ratio, WidthScalarWork.ratio_value] using he
    ⟨some ⟨xy.1, xy.2, (scaleWitness_some s p.R hxy).1, (scaleWitness_some s p.R hxy).2⟩,
      ratio.work + chosen.work + 2⟩

@[simp] theorem select_value (a : LocalAccess s) (p : ScaleParameters) :
    (select a p).value = selectScale s p := by
  simp only [select, selectScale]
  split <;> split
  all_goals
    have hr := WidthScalarWork.ratio_value p
    have hs := RepairSelectWork.scaleWitness_value a (WidthScalarWork.ratio p).value
    aesop

def workBound (n A : ℕ) (p : ScaleParameters) : ℕ :=
  4 * p.H + 2 * p.J + 16 + RepairSelectWork.scaleBound n A + 2

theorem select_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (p : ScaleParameters) :
    (select a p).work ≤ workBound n A p := by
  have hh := RepairSelectWork.scaleWitness_work_le a h (WidthScalarWork.ratio p).value
  simp only [select]
  split <;> dsimp only <;> rw [WidthScalarWork.ratio_work] <;> unfold workBound <;> omega

end SortingAdversary.Optimal.MeasuredScaleDecision
