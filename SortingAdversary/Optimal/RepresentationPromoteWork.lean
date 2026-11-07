import SortingAdversary.Optimal.RepresentationPromotion

/-!
# Actual promotion work and eager cache costs

The measured branch tests select exactly the original parent update. The
resulting getters are then materialized, giving the next primitive operation
constant-time access to all retained fields.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair FiniteRefinement

variable {n : ℕ} {s t : State n}

namespace LocalAccess

def transport (he : s = t) (a : LocalAccess s) : LocalAccess t := he ▸ a

theorem transport_bound (he : s = t) (a : LocalAccess s) {A : ℕ} (h : AccessBound a A) :
    AccessBound (a.transport he) A := by cases he; exact h

end LocalAccess

theorem lowerPromotionAccess_bound (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hl : s.pool.system.effectiveLower v = c) :
    AccessBound (lowerPromotionAccess a v hv c hl) (2 * A + 16) := by
  constructor
  · intro x y; exact (h.publicRow x y).trans (by omega)
  · intro x y; exact (h.source x y).trans (by omega)
  · intro x y
    have hh := h.active x y
    change (a.active x y).work + 4 ≤ _
    omega
  · intro x
    have hh := splitWall_work_le a.pin a.lower (embedAfter c) (embedAfter c) x A 3
      (h.pin x) (h.lower x) (fun _ => le_rfl) (fun _ => le_rfl)
    change (splitWall a.pin a.lower (embedAfter c) (embedAfter c) x).work + 3 ≤ _
    omega
  · intro x
    have hh := splitWall_work_le a.pin a.upper (embedAfter c) (embedUpper c) x A 3
      (h.pin x) (h.upper x) (fun _ => le_rfl) (fun _ => le_rfl)
    change (splitWall a.pin a.upper (embedAfter c) (embedUpper c) x).work + 3 ≤ _
    omega
  · intro x
    exact (pinMap_work_le a.pin (embedAfter c) v (freshColor c) x A 3
      (h.pin x) (fun _ => le_rfl)).trans (by omega)
  · intro x; exact (h.member x).trans (by omega)
  · intro x; exact (extendForward_work_le a.order (freshColor c) x A h.order).trans (by omega)
  · intro x; exact (extendInverse_work_le a.inverse (freshColor c) x A h.inverse).trans (by omega)

theorem upperPromotionAccess_bound (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hu : s.pool.system.effectiveUpper v = c) :
    AccessBound (upperPromotionAccess a v hv c hu) (2 * A + 16) := by
  constructor
  · intro x y; exact (h.publicRow x y).trans (by omega)
  · intro x y; exact (h.source x y).trans (by omega)
  · intro x y
    have hh := h.active x y
    change (a.active x y).work + 4 ≤ _
    omega
  · intro x
    have hh := splitWall_work_le a.pin a.lower (embedBefore c) (embedAfter c) x A 3
      (h.pin x) (h.lower x) (fun _ => le_rfl) (fun _ => le_rfl)
    change (splitWall a.pin a.lower (embedBefore c) (embedAfter c) x).work + 3 ≤ _
    omega
  · intro x
    have hh := splitWall_work_le a.pin a.upper (embedBefore c) (embedUpper c) x A 3
      (h.pin x) (h.upper x) (fun _ => le_rfl) (fun _ => le_rfl)
    change (splitWall a.pin a.upper (embedBefore c) (embedUpper c) x).work + 3 ≤ _
    omega
  · intro x
    exact (pinMap_work_le a.pin (embedBefore c) v c.castSucc x A 3
      (h.pin x) (fun _ => le_rfl)).trans (by omega)
  · intro x; exact (h.member x).trans (by omega)
  · intro x; exact (extendForward_work_le a.order c.castSucc x A h.order).trans (by omega)
  · intro x; exact (extendInverse_work_le a.inverse c.castSucc x A h.inverse).trans (by omega)

theorem interiorPromotionAccess_bound (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    AccessBound (interiorPromotionAccess a v hv c hc) (2 * A + 16) := by
  constructor
  · intro x y; exact (h.publicRow x y).trans (by omega)
  · intro x y; exact (h.source x y).trans (by omega)
  · intro x y
    have hh := h.active x y
    change (a.active x y).work + 4 ≤ _
    omega
  · intro x
    have hh := h.lower x
    change (a.lower x).work + 3 ≤ _
    omega
  · intro x
    have hh := h.upper x
    change (a.upper x).work + 3 ≤ _
    omega
  · intro x
    exact (pinMap_work_le a.pin (fun c => ⟨c, 0⟩) v c x A 0
      (h.pin x) (fun _ => le_rfl)).trans (by omega)
  · intro x; exact (h.member x).trans (by omega)
  · intro x; exact (h.order x).trans (by omega)
  · intro x; exact (h.inverse x).trans (by omega)

namespace LocalAccess

def promote (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    Result (LocalAccess (s.promote v hv c hc)) :=
  let lower := WindowWork.effectiveLower a.windows v
  let upper := WindowWork.effectiveUpper a.windows v
  if hl : lower.value = c then
    have hl' : s.pool.system.effectiveLower v = c := by simpa only
      [lower, WindowWork.effectiveLower_value, windows_system] using hl
    ⟨(lowerPromotionAccess a v hv c hl').transport (lowerState_actual s v hv c hc hl'),
      lower.work + upper.work + 24⟩
  else if hu : upper.value = c then
    have hl' : s.pool.system.effectiveLower v ≠ c := by simpa only
      [lower, WindowWork.effectiveLower_value, windows_system] using hl
    have hu' : s.pool.system.effectiveUpper v = c := by simpa only
      [upper, WindowWork.effectiveUpper_value, windows_system] using hu
    ⟨(upperPromotionAccess a v hv c hu').transport (upperState_actual s v hv c hc hl' hu'),
      lower.work + upper.work + 24⟩
  else
    have hl' : s.pool.system.effectiveLower v ≠ c := by simpa only
      [lower, WindowWork.effectiveLower_value, windows_system] using hl
    have hu' : s.pool.system.effectiveUpper v ≠ c := by simpa only
      [upper, WindowWork.effectiveUpper_value, windows_system] using hu
    have interior : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v :=
      ⟨lt_of_le_of_ne hc.1 hl', lt_of_le_of_ne hc.2 hu'.symm⟩
    ⟨(interiorPromotionAccess a v hv c interior).transport (interiorState_actual s v hv c interior),
      lower.work + upper.work + 24⟩

theorem promote_access (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    AccessBound (a.promote v hv c hc).value (2 * A + 16) := by
  unfold promote
  dsimp only
  split
  · exact transport_bound _ _ (lowerPromotionAccess_bound a h v hv c _)
  · split
    · exact transport_bound _ _ (upperPromotionAccess_bound a h v hv c _)
    · exact transport_bound _ _ (interiorPromotionAccess_bound a h v hv c _)

theorem promote_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (a.promote v hv c hc).work ≤ 2 * WindowWork.endpointWorkBound n A A + 24 := by
  have hl := WindowWork.effectiveLower_work_le a.windows v A A (fun u => h.publicRow u v) h.lower
  have hu := WindowWork.effectiveUpper_work_le a.windows v A A (h.publicRow v) h.upper
  unfold promote
  dsimp only
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

def promoteCached (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    Result (LocalAccess (s.promote v hv c hc)) :=
  let updated := a.promote v hv c hc
  let cached := updated.value.cache
  ⟨cached.value, updated.work + cached.work⟩

theorem promoteCached_access (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    AccessBound (a.promoteCached v hv c hc).value 2 :=
  cache_access _

theorem promoteCached_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (a.promoteCached v hv c hc).work ≤ 2 * WindowWork.endpointWorkBound n A A + 24 +
      cacheBound n (s.promote v hv c hc).pool.palette (2 * A + 16) := by
  exact Nat.add_le_add (promote_work_le a h v hv c hc)
    (cache_work_le _ (promote_access a h v hv c hc))

end LocalAccess

end SortingAdversary.Optimal.RepresentationWork
