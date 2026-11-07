import SortingAdversary.Optimal.RepresentationTreeAdmission

/-!
# Measured immutable-colour transport for an actual promotion

The endpoint tests are computed from the measured public relation and
primitive walls. Each resulting key closure performs only its paid scalar
embedding arithmetic. Its destination is the actual new colour when an
endpoint refinement creates one.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState FiniteRefinement

variable {n : ℕ} {s : State n}

structure PromotionKeys {v : Fin n} {c : Fin (s.pool.palette + 1)}
    (r : Promotion.Result s.pool.system s.pool.pins v c) where
  key : ℕ → Result ℕ
  destination : ℕ
  palette : ℕ
  key_value : ∀ i, (key i).value = ColourTransport.extend r.embed i
  destination_value : destination = r.destination.val
  palette_value : palette = r.palette

namespace PromotionKeys

def transport {v : Fin n} {c : Fin (s.pool.palette + 1)}
    {r q : Promotion.Result s.pool.system s.pool.pins v c} (he : r = q)
    (a : PromotionKeys r) : PromotionKeys q := he ▸ a

def Bound {v : Fin n} {c : Fin (s.pool.palette + 1)}
    {r : Promotion.Result s.pool.system s.pool.pins v c} (a : PromotionKeys r) (A : ℕ) : Prop :=
  ∀ i, (a.key i).work ≤ A

theorem transport_bound {v : Fin n} {c : Fin (s.pool.palette + 1)}
    {r q : Promotion.Result s.pool.system s.pool.pins v c} (he : r = q)
    (a : PromotionKeys r) {A : ℕ} (h : a.Bound A) : (a.transport he).Bound A := by
  cases he
  exact h

def lower (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hl : s.pool.system.effectiveLower v = c) :
    PromotionKeys (lowerResult s v hv c hl) where
  key i := extendKey (K := s.pool.palette + 1) (L := s.pool.palette + 2) (fun x => embedAfter c x) i
  destination := c.val + 1
  palette := s.pool.palette + 1
  key_value i := extendKey_value (embedAfter c) (embedColor c) (fun _ => rfl) i
  destination_value := rfl
  palette_value := rfl

def upper (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hu : s.pool.system.effectiveUpper v = c) :
    PromotionKeys (upperResult s v hv c hu) where
  key i := extendKey (K := s.pool.palette + 1) (L := s.pool.palette + 2) (fun x => embedBefore c x) i
  destination := c.val
  palette := s.pool.palette + 1
  key_value i := extendKey_value (embedBefore c) (embedColorBefore c) (fun _ => rfl) i
  destination_value := rfl
  palette_value := rfl

def interior (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    PromotionKeys (s.interiorResult v c hc) where
  key j := extendKey (K := s.pool.palette + 1) (L := s.pool.palette + 1)
    (fun (i : Fin (s.pool.palette + 1)) => ⟨i, 0⟩) j
  destination := c.val
  palette := s.pool.palette
  key_value i := extendKey_value _ id (fun _ => rfl) i
  destination_value := rfl
  palette_value := rfl

theorem lower_bound (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hl : s.pool.system.effectiveLower v = c) :
    (lower s v hv c hl).Bound 7 :=
  fun i => extendKey_work _ (C := 3) (fun _ => le_rfl) i

theorem upper_bound (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hu : s.pool.system.effectiveUpper v = c) :
    (upper s v hv c hu).Bound 7 :=
  fun i => extendKey_work _ (C := 3) (fun _ => le_rfl) i

theorem interior_bound (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    (interior s v c hc).Bound 7 :=
  fun i => (extendKey_work _ (C := 0) (fun _ => le_rfl) i).trans (by omega)

end PromotionKeys

namespace LocalAccess

def promotionKeys (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    Result (PromotionKeys (Promotion.promote s.pool.system s.pool.pins s.pool.invariant
      s.pool.pin_bounds v hv c hc)) :=
  let lower := WindowWork.effectiveLower a.windows v
  let upper := WindowWork.effectiveUpper a.windows v
  if hl : lower.value = c then
    have hl' : s.pool.system.effectiveLower v = c := by
      simpa only [lower, WindowWork.effectiveLower_value, windows_system] using hl
    ⟨(PromotionKeys.lower s v hv c hl').transport (lowerResult_actual s v hv c hc hl'),
      lower.work + upper.work + 8⟩
  else if hu : upper.value = c then
    have hl' : s.pool.system.effectiveLower v ≠ c := by
      simpa only [lower, WindowWork.effectiveLower_value, windows_system] using hl
    have hu' : s.pool.system.effectiveUpper v = c := by
      simpa only [upper, WindowWork.effectiveUpper_value, windows_system] using hu
    ⟨(PromotionKeys.upper s v hv c hu').transport (upperResult_actual s v hv c hc hl' hu'),
      lower.work + upper.work + 8⟩
  else
    have hl' : s.pool.system.effectiveLower v ≠ c := by
      simpa only [lower, WindowWork.effectiveLower_value, windows_system] using hl
    have hu' : s.pool.system.effectiveUpper v ≠ c := by
      simpa only [upper, WindowWork.effectiveUpper_value, windows_system] using hu
    have hi : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v :=
      ⟨lt_of_le_of_ne hc.1 hl', lt_of_le_of_ne hc.2 (Ne.symm hu')⟩
    ⟨(PromotionKeys.interior s v c hi).transport (s.interiorResult_actual v hv c hi),
      lower.work + upper.work + 8⟩

theorem promotionKeys_bound (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (a.promotionKeys v hv c hc).value.Bound 7 := by
  unfold promotionKeys
  dsimp only
  split
  · exact PromotionKeys.transport_bound _ _ (PromotionKeys.lower_bound s v hv c _)
  · split
    · exact PromotionKeys.transport_bound _ _ (PromotionKeys.upper_bound s v hv c _)
    · exact PromotionKeys.transport_bound _ _ (PromotionKeys.interior_bound s v c _)

theorem promotionKeys_work (a : LocalAccess s) {A : ℕ} (ha : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (a.promotionKeys v hv c hc).work ≤ 2 * WindowWork.endpointWorkBound n A A + 8 := by
  have hl := WindowWork.effectiveLower_work_le a.windows v A A (fun u => ha.publicRow u v) ha.lower
  have hu := WindowWork.effectiveUpper_work_le a.windows v A A (ha.publicRow v) ha.upper
  unfold promotionKeys
  dsimp only
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

def pinKeys (a : LocalAccess s) (update : PinUpdate s) : Result (PromotionKeys update.result) :=
  let keys := a.promotionKeys update.vertex update.free update.colour update.supported
  ⟨keys.value.transport update.actual.symm, keys.work⟩

theorem pinKeys_bound (a : LocalAccess s) (update : PinUpdate s) :
    (a.pinKeys update).value.Bound 7 :=
  PromotionKeys.transport_bound _ _ (a.promotionKeys_bound update.vertex update.free update.colour update.supported)

theorem pinKeys_work (a : LocalAccess s) {A : ℕ} (ha : AccessBound a A) (update : PinUpdate s) :
    (a.pinKeys update).work ≤ 2 * WindowWork.endpointWorkBound n A A + 8 :=
  a.promotionKeys_work ha ..

end LocalAccess

end SortingAdversary.Optimal.RepresentationWork
