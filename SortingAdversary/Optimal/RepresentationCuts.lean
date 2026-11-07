import SortingAdversary.Optimal.RepresentationPromoteWork
import SortingAdversary.Optimal.RepresentationCacheShape

/-!
# Measured strict cuts of primitive walls

Each propagated threshold is computed once and captured by the two updated
wall getters. The source relation is preserved and exactly one active row is
retired. The following eager cache pays for every retained getter call.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair CutNormalization

variable {n : ℕ} {s : State n}

def lowerCutAccess (a : LocalAccess s) (u v : Fin n) (live : s.rows.active u v = true)
    (ratio : 2 * s.width v < s.width u) (threshold : Fin (s.pool.palette + 1))
    (ht : threshold = s.pool.system.effectiveLower v) : LocalAccess (s.lowerCut u v live ratio) where
  publicRow := a.publicRow
  source := a.source
  active := eraseRow a.active u v
  lower := pinLower a.lower v threshold
  upper := pinUpper a.upper u (previousColor threshold)
  pin := a.pin
  member := a.member
  order := a.order
  inverse := a.inverse
  publicRow_value := a.publicRow_value
  source_value := a.source_value
  active_value x y := (eraseRow_value a u v x y).trans
    (congrArg (fun r => r x y) (s.lowerCut_active u v live ratio)).symm
  lower_value x := by simp only [pinLower, a.lower_value, ht]; rfl
  upper_value x := by simp only [pinUpper, a.upper_value, ht]; rfl
  pin_value := a.pin_value
  member_value := a.member_value
  order_value := a.order_value
  inverse_value := a.inverse_value

def upperCutAccess (a : LocalAccess s) (u v : Fin n) (live : s.rows.active u v = true)
    (ratio : 2 * s.width u < s.width v) (threshold : Fin (s.pool.palette + 1))
    (ht : threshold = s.pool.system.effectiveUpper u) : LocalAccess (s.upperCut u v live ratio) where
  publicRow := a.publicRow
  source := a.source
  active := eraseRow a.active u v
  lower := pinLower a.lower v (nextColor threshold)
  upper := pinUpper a.upper u threshold
  pin := a.pin
  member := a.member
  order := a.order
  inverse := a.inverse
  publicRow_value := a.publicRow_value
  source_value := a.source_value
  active_value x y := (eraseRow_value a u v x y).trans
    (congrArg (fun r => r x y) (s.upperCut_active u v live ratio)).symm
  lower_value x := by simp only [pinLower, a.lower_value, ht]; rfl
  upper_value x := by simp only [pinUpper, a.upper_value, ht]; rfl
  pin_value := a.pin_value
  member_value := a.member_value
  order_value := a.order_value
  inverse_value := a.inverse_value

theorem lowerCutAccess_bound (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width v < s.width u)
    (threshold : Fin (s.pool.palette + 1)) (ht : threshold = s.pool.system.effectiveLower v) :
    AccessBound (lowerCutAccess a u v live ratio threshold ht) (2 * A + 16) := by
  constructor
  · intro x y; exact (h.publicRow x y).trans (by omega)
  · intro x y; exact (h.source x y).trans (by omega)
  · intro x y; have hh := h.active x y; change (a.active x y).work + 4 ≤ _; omega
  · intro x; have hh := h.lower x; change (a.lower x).work + 3 ≤ _; omega
  · intro x; have hh := h.upper x; change (a.upper x).work + 3 ≤ _; omega
  · intro x; exact (h.pin x).trans (by omega)
  · intro x; exact (h.member x).trans (by omega)
  · intro x; exact (h.order x).trans (by omega)
  · intro x; exact (h.inverse x).trans (by omega)

theorem upperCutAccess_bound (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width u < s.width v)
    (threshold : Fin (s.pool.palette + 1)) (ht : threshold = s.pool.system.effectiveUpper u) :
    AccessBound (upperCutAccess a u v live ratio threshold ht) (2 * A + 16) := by
  constructor
  · intro x y; exact (h.publicRow x y).trans (by omega)
  · intro x y; exact (h.source x y).trans (by omega)
  · intro x y; have hh := h.active x y; change (a.active x y).work + 4 ≤ _; omega
  · intro x; have hh := h.lower x; change (a.lower x).work + 3 ≤ _; omega
  · intro x; have hh := h.upper x; change (a.upper x).work + 3 ≤ _; omega
  · intro x; exact (h.pin x).trans (by omega)
  · intro x; exact (h.member x).trans (by omega)
  · intro x; exact (h.order x).trans (by omega)
  · intro x; exact (h.inverse x).trans (by omega)

namespace LocalAccess

def lowerCut (a : LocalAccess s) (u v : Fin n) (live : s.rows.active u v = true)
    (ratio : 2 * s.width v < s.width u) : Result (LocalAccess (s.lowerCut u v live ratio)) :=
  let threshold := WindowWork.effectiveLower a.windows v
  ⟨lowerCutAccess a u v live ratio threshold.value
    (by simp only [threshold, WindowWork.effectiveLower_value, windows_system]), threshold.work + 16⟩

def upperCut (a : LocalAccess s) (u v : Fin n) (live : s.rows.active u v = true)
    (ratio : 2 * s.width u < s.width v) : Result (LocalAccess (s.upperCut u v live ratio)) :=
  let threshold := WindowWork.effectiveUpper a.windows u
  ⟨upperCutAccess a u v live ratio threshold.value
    (by simp only [threshold, WindowWork.effectiveUpper_value, windows_system]), threshold.work + 16⟩

theorem lowerCut_access (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width v < s.width u) :
    AccessBound (a.lowerCut u v live ratio).value (2 * A + 16) :=
  lowerCutAccess_bound a h u v live ratio _
    (by simp only [WindowWork.effectiveLower_value, windows_system])

theorem upperCut_access (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width u < s.width v) :
    AccessBound (a.upperCut u v live ratio).value (2 * A + 16) :=
  upperCutAccess_bound a h u v live ratio _
    (by simp only [WindowWork.effectiveUpper_value, windows_system])

theorem lowerCut_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width v < s.width u) :
    (a.lowerCut u v live ratio).work ≤ WindowWork.endpointWorkBound n A A + 16 :=
  Nat.add_le_add_right
    (WindowWork.effectiveLower_work_le a.windows v A A (fun x => h.publicRow x v) h.lower) 16

theorem upperCut_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width u < s.width v) :
    (a.upperCut u v live ratio).work ≤ WindowWork.endpointWorkBound n A A + 16 :=
  Nat.add_le_add_right
    (WindowWork.effectiveUpper_work_le a.windows u A A (h.publicRow u) h.upper) 16

def lowerCutCached (a : LocalAccess s) (u v : Fin n) (live : s.rows.active u v = true)
    (ratio : 2 * s.width v < s.width u) : Result (LocalAccess (s.lowerCut u v live ratio)) :=
  let updated := a.lowerCut u v live ratio
  let cached := updated.value.cacheWith s.pool.palette rfl
  ⟨cached.value, updated.work + cached.work⟩

def upperCutCached (a : LocalAccess s) (u v : Fin n) (live : s.rows.active u v = true)
    (ratio : 2 * s.width u < s.width v) : Result (LocalAccess (s.upperCut u v live ratio)) :=
  let updated := a.upperCut u v live ratio
  let cached := updated.value.cacheWith s.pool.palette rfl
  ⟨cached.value, updated.work + cached.work⟩

theorem lowerCutCached_access (a : LocalAccess s) (u v : Fin n)
    (live : s.rows.active u v = true) (ratio : 2 * s.width v < s.width u) :
    AccessBound (a.lowerCutCached u v live ratio).value 2 := cacheWith_access _ _ rfl

theorem upperCutCached_access (a : LocalAccess s) (u v : Fin n)
    (live : s.rows.active u v = true) (ratio : 2 * s.width u < s.width v) :
    AccessBound (a.upperCutCached u v live ratio).value 2 := cacheWith_access _ _ rfl

theorem lowerCutCached_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width v < s.width u) :
    (a.lowerCutCached u v live ratio).work ≤ WindowWork.endpointWorkBound n A A + 16 +
      cacheBound n s.pool.palette (2 * A + 16) :=
  Nat.add_le_add (lowerCut_work_le a h u v live ratio) (cacheWith_work_le _ _ rfl (lowerCut_access a h u v live ratio))

theorem upperCutCached_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (u v : Fin n) (live : s.rows.active u v = true) (ratio : 2 * s.width u < s.width v) :
    (a.upperCutCached u v live ratio).work ≤ WindowWork.endpointWorkBound n A A + 16 +
      cacheBound n s.pool.palette (2 * A + 16) :=
  Nat.add_le_add (upperCut_work_le a h u v live ratio) (cacheWith_work_le _ _ rfl (upperCut_access a h u v live ratio))

end LocalAccess

end SortingAdversary.Optimal.RepresentationWork
