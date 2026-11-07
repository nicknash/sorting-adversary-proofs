import SortingAdversary.Optimal.PrimitiveWork
import SortingAdversary.Optimal.WidthRepair

/-! Count every copied trace cell when chronological repair traces are joined. -/

namespace SortingAdversary.Optimal.TraceAppendWork

open PrimitiveWork WidthRepair

variable {n : ℕ}

def append : {s t u : State n} → Trace s t → Trace t u → Result (Trace s u)
  | _, _, _, .nil _, second => ⟨second, 1⟩
  | _, _, _, .cons head rest, second =>
    let tail := append rest second
    ⟨.cons head tail.value, tail.work + 2⟩

@[simp] theorem append_value {s t u : State n} (first : Trace s t) (second : Trace t u) :
    (append first second).value = first.append second := by
  induction first with
  | nil => rfl
  | cons head rest ih => simp only [append, Trace.append, ih]

@[simp] theorem append_work {s t u : State n} (first : Trace s t) (second : Trace t u) :
    (append first second).work = 2 * first.length + 1 := by
  induction first with
  | nil => rfl
  | cons head rest ih =>
    simp only [append, Trace.length, ih]
    omega

end SortingAdversary.Optimal.TraceAppendWork
