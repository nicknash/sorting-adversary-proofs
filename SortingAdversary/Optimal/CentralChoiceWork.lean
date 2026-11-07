import SortingAdversary.Optimal.RepresentationCells
import SortingAdversary.Optimal.WidthInterior

/-!
# Measured central insertion coordinates

Both effective endpoints are scanned once. The common quarter-width is
computed once and reused for the two half-open endpoints. The selected cheap
colour is the first central position, exactly as in the executable adversary.
The sparse closed numerical view has the same endpoints; no closure is
recomputed in order to obtain these coordinates.
-/

namespace SortingAdversary.Optimal.CentralChoiceWork

open PrimitiveWork RepresentationWork WidthRepair

variable {n : ℕ} {s : State n}

def interval (a : LocalAccess s) (v : Fin n) : Result (ℕ × ℕ) :=
  let lower := WindowWork.effectiveLower a.windows v
  let upper := WindowWork.effectiveUpper a.windows v
  let quarter := (upper.value.val - lower.value.val) / 4
  ⟨(lower.value.val + quarter, upper.value.val - quarter + 1), lower.work + upper.work + 5⟩

@[simp] theorem interval_value (a : LocalAccess s) (v : Fin n) :
    (interval a v).value =
      (ScaleMass.intervalLower s.numerical v, ScaleMass.intervalUpper s.numerical v) := by
  have hw := s.numerical_windows v
  simp only [interval, WindowWork.effectiveLower_value, WindowWork.effectiveUpper_value,
    LocalAccess.windows_system, ScaleMass.intervalLower, ScaleMass.intervalUpper,
    ScaleMass.centralLower, ScaleMass.centralUpper, hw.1, hw.2]

def workBound (n A : ℕ) : ℕ := 2 * WindowWork.endpointWorkBound n A A + 5

theorem interval_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (v : Fin n) :
    (interval a v).work ≤ workBound n A := by
  have hl := WindowWork.effectiveLower_work_le a.windows v A A (fun u => h.publicRow u v) h.lower
  have hu := WindowWork.effectiveUpper_work_le a.windows v A A (h.publicRow v) h.upper
  change _ + _ + 5 ≤ _
  unfold workBound
  omega

def colour (a : LocalAccess s) (v : Fin n) : Result (Fin (s.pool.palette + 1)) :=
  let endpoints := interval a v
  ⟨⟨endpoints.value.1, by
      rw [show endpoints.value.1 = ScaleMass.intervalLower s.numerical v from
        congrArg Prod.fst (interval_value a v)]
      exact (s.centralColour v).isLt⟩, endpoints.work + 1⟩

@[simp] theorem colour_value (a : LocalAccess s) (v : Fin n) :
    (colour a v).value = s.centralColour v := by
  apply Fin.ext
  exact congrArg Prod.fst (interval_value a v)

theorem colour_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) (v : Fin n) :
    (colour a v).work ≤ workBound n A + 1 := Nat.add_le_add_right (interval_work_le a h v) 1

end SortingAdversary.Optimal.CentralChoiceWork
