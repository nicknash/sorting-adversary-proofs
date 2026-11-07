import SortingAdversary.Optimal.RepresentationCuts

/-!
# Cached representation updates along actual primitive traces

This module executes the getter updates, including their eager caches. The
trace's selection and control costs are separate: the measured normalizer
must generate that trace using the measured selectors. The replay here pays
for each concrete state transformation and proves its representation bound.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair

variable {n : ℕ} {s t : State n}

theorem step_palette_le (step : Step s t) : t.pool.palette ≤ s.pool.palette + 1 := by
  cases step with
  | pin update => exact update.result.palette_bounds.2
  | lowerCut => exact Nat.le_succ _
  | upperCut => exact Nat.le_succ _

theorem trace_palette_le (trace : Trace s t) : t.pool.palette ≤ s.pool.palette + trace.length := by
  induction trace with
  | nil => simp only [Trace.length]; omega
  | cons head tail ih =>
    have hh := step_palette_le head
    simp only [Trace.length]
    omega

namespace LocalAccess

theorem cacheBound_mono {n K L A B : ℕ} (hK : K ≤ L) (hA : A ≤ B) :
    cacheBound n K A ≤ cacheBound n L B := by
  unfold cacheBound
  gcongr

def step (a : LocalAccess s) (transition : Step s t) : Result (LocalAccess t) :=
  match transition with
  | .pin update =>
    let updated := a.promoteCached update.vertex update.free update.colour update.supported
    ⟨updated.value.transport (pinUpdate_next_eq_promote update).symm, updated.work⟩
  | .lowerCut _ u v live ratio _ _ => a.lowerCutCached u v live ratio
  | .upperCut _ u v live ratio _ _ => a.upperCutCached u v live ratio

theorem step_access (a : LocalAccess s) (transition : Step s t) :
    AccessBound (a.step transition).value 2 := by
  cases transition with
  | pin update => exact transport_bound _ _ (promoteCached_access a _ _ _ _)
  | lowerCut => exact lowerCutCached_access a _ _ _ _
  | upperCut => exact upperCutCached_access a _ _ _ _

def updateBound (n palette A : ℕ) : ℕ :=
  2 * WindowWork.endpointWorkBound n A A + 24 + cacheBound n (palette + 1) (2 * A + 16)

theorem updateBound_mono {n K L A : ℕ} (hK : K ≤ L) :
    updateBound n K A ≤ updateBound n L A := by
  unfold updateBound
  exact Nat.add_le_add_left (cacheBound_mono (Nat.succ_le_succ hK) le_rfl) _

theorem step_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (transition : Step s t) : (a.step transition).work ≤ updateBound n s.pool.palette A := by
  cases transition with
  | pin update =>
    have hp := promoteCached_work_le a h update.vertex update.free update.colour update.supported
    have hK : (s.promote update.vertex update.free update.colour update.supported).pool.palette ≤
        s.pool.palette + 1 := by
      rw [← pinUpdate_next_eq_promote update]
      exact update.result.palette_bounds.2
    exact hp.trans (Nat.add_le_add_left (cacheBound_mono hK le_rfl) _)
  | lowerCut u v live ratio _ _ =>
    have hp := lowerCutCached_work_le a h u v live ratio
    have hc := cacheBound_mono (n := n) (A := 2 * A + 16) (Nat.le_succ s.pool.palette) le_rfl
    simp only [Nat.succ_eq_add_one] at hc
    unfold updateBound
    exact hp.trans (by omega)
  | upperCut u v live ratio _ _ =>
    have hp := upperCutCached_work_le a h u v live ratio
    have hc := cacheBound_mono (n := n) (A := 2 * A + 16) (Nat.le_succ s.pool.palette) le_rfl
    simp only [Nat.succ_eq_add_one] at hc
    unfold updateBound
    exact hp.trans (by omega)

def trace : {s t : State n} → (a : LocalAccess s) → Trace s t → Result (LocalAccess t)
  | _, _, a, .nil _ => ⟨a, 1⟩
  | _, _, a, .cons first rest =>
    let updated := a.step first
    let final := updated.value.trace rest
    ⟨final.value, updated.work + final.work + 2⟩

theorem trace_access (a : LocalAccess s) (h : AccessBound a 2) (transitions : Trace s t) :
    AccessBound (a.trace transitions).value 2 := by
  induction transitions with
  | nil => exact h
  | cons first rest ih => exact ih _ (step_access a first)

/-- Every intermediate palette grows by at most the number of preceding
pins, and that number is bounded by the actual primitive trace length. -/
theorem trace_work_le (a : LocalAccess s) (h : AccessBound a 2) (transitions : Trace s t) :
    (a.trace transitions).work ≤
      transitions.length * (updateBound n (s.pool.palette + transitions.length) 2 + 2) + 1 := by
  induction transitions with
  | nil => simp only [trace, Trace.length, Nat.zero_mul, Nat.zero_add]; exact le_rfl
  | @cons s mid t first rest ih =>
    have hs := step_work_le a h first
    have hr := ih (a.step first).value (step_access a first)
    have hK := step_palette_le first
    have hb0 : updateBound n s.pool.palette 2 ≤
        updateBound n (s.pool.palette + (Trace.cons first rest).length) 2 :=
      updateBound_mono (Nat.le_add_right _ _)
    have hb1 : updateBound n (mid.pool.palette + rest.length) 2 ≤
        updateBound n (s.pool.palette + (Trace.cons first rest).length) 2 :=
      updateBound_mono (by simp only [Trace.length]; omega)
    have hmul := Nat.mul_le_mul_left rest.length (Nat.add_le_add_right hb1 2)
    change (a.step first).work + ((a.step first).value.trace rest).work + 2 ≤ _
    simp only [Trace.length, Nat.add_mul, one_mul] at hb0 hb1 hmul ⊢
    omega

end LocalAccess

end SortingAdversary.Optimal.RepresentationWork
