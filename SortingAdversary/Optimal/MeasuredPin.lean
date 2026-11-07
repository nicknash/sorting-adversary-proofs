import SortingAdversary.Optimal.RepresentationTrace
import SortingAdversary.Optimal.RepresentationCacheShape

/-!
# A measured physical pin with its actual replayable update

The endpoint branches are chosen by measured window scans. Each branch
constructs its concrete result, sparse metadata and palette permutation,
then materializes the updated getters. The canonical promotion appears only
in erased correctness certificates; it is never called to select a runtime
branch or to provide an already computed output.
-/

namespace SortingAdversary.Optimal.MeasuredPin

open PrimitiveWork WidthRepair PoolState RepresentationWork SeparatedPins

variable {n : ℕ} {s : State n}

def canonical (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc).system.count) :
    PinUpdate s where
  vertex := v
  free := hv
  colour := c
  supported := hc
  mate := hm
  result := Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc
  actual := rfl
  data := s.promotionData v hv c hc
  charge := charge
  retained := retained

theorem update_ext (first second : PinUpdate s)
    (hv : first.vertex = second.vertex) (hc : first.colour = second.colour)
    (hcharge : first.charge = second.charge) : first = second := by
  cases first with
  | mk v vf c cs vm result actual data charge retained =>
    cases second with
    | mk w wf d ds wm result' actual' data' charge' retained' =>
      dsimp only at hv hc hcharge
      cases hv
      cases hc
      cases hcharge
      have hr := actual.trans actual'.symm
      cases hr
      have hd := promotionData_unique data data'
      cases hd
      rfl

def fromResult (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc).system.count)
    (result : Promotion.Result s.pool.system s.pool.pins v c)
    (actual : result = Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc)
    (data : State.PromotionData s v c result) : PinUpdate s where
  vertex := v
  free := hv
  colour := c
  supported := hc
  mate := hm
  result := result
  actual := actual
  data := data
  charge := charge
  retained := by rw [actual]; exact retained

theorem fromResult_eq (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc).system.count)
    (result : Promotion.Result s.pool.system s.pool.pins v c)
    (actual : result = Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc)
    (data : State.PromotionData s v c result) :
    fromResult s v hv c hc hm charge retained result actual data =
      canonical s v hv c hc hm charge retained := update_ext _ _ rfl rfl rfl

structure Output (expected : PinUpdate s) where
  update : PinUpdate s
  access : LocalAccess update.next
  exact : update = expected
  bounded : AccessBound access 2

def pin (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc).system.count) :
    Result (Output (canonical s v hv c hc hm charge retained)) :=
  let lower := WindowWork.effectiveLower a.windows v
  let upper := WindowWork.effectiveUpper a.windows v
  if hl : lower.value = c then
    have hl' : s.pool.system.effectiveLower v = c := by
      simpa only [lower, WindowWork.effectiveLower_value, LocalAccess.windows_system] using hl
    let update := fromResult s v hv c hc hm charge retained
      (lowerResult s v hv c hl') (lowerResult_actual s v hv c hc hl') (lowerData s v hv c hl')
    let cached := (lowerPromotionAccess a v hv c hl').cacheWith (s.pool.palette + 1) rfl
    ⟨⟨update, cached.value, fromResult_eq .., LocalAccess.cacheWith_access _ _ rfl⟩, lower.work + upper.work + cached.work + 32⟩
  else if hu : upper.value = c then
    have hl' : s.pool.system.effectiveLower v ≠ c := by
      simpa only [lower, WindowWork.effectiveLower_value, LocalAccess.windows_system] using hl
    have hu' : s.pool.system.effectiveUpper v = c := by
      simpa only [upper, WindowWork.effectiveUpper_value, LocalAccess.windows_system] using hu
    let update := fromResult s v hv c hc hm charge retained
      (upperResult s v hv c hu') (upperResult_actual s v hv c hc hl' hu') (upperData s v hv c hu')
    let cached := (upperPromotionAccess a v hv c hu').cacheWith (s.pool.palette + 1) rfl
    ⟨⟨update, cached.value, fromResult_eq .., LocalAccess.cacheWith_access _ _ rfl⟩, lower.work + upper.work + cached.work + 32⟩
  else
    have hl' : s.pool.system.effectiveLower v ≠ c := by
      simpa only [lower, WindowWork.effectiveLower_value, LocalAccess.windows_system] using hl
    have hu' : s.pool.system.effectiveUpper v ≠ c := by
      simpa only [upper, WindowWork.effectiveUpper_value, LocalAccess.windows_system] using hu
    have interior : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v :=
      ⟨lt_of_le_of_ne hc.1 hl', lt_of_le_of_ne hc.2 hu'.symm⟩
    let update := fromResult s v hv c hc hm charge retained
      (s.interiorResult v c interior) (s.interiorResult_actual v hv c interior) (interiorData s v c interior)
    let cached := (interiorPromotionAccess a v hv c interior).cacheWith s.pool.palette rfl
    ⟨⟨update, cached.value, fromResult_eq .., LocalAccess.cacheWith_access _ _ rfl⟩, lower.work + upper.work + cached.work + 32⟩

theorem pin_access (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc).system.count) :
    AccessBound (pin a v hv c hc hm charge retained).value.access 2 :=
  (pin a v hv c hc hm charge retained).value.bounded

def workBound (n palette A : ℕ) : ℕ :=
  2 * WindowWork.endpointWorkBound n A A + 32 + LocalAccess.cacheBound n (palette + 1) (2 * A + 16)

theorem pin_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hm : HasMate s.pool v) (charge : ℚ)
    (retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc).system.count) :
    (pin a v hv c hc hm charge retained).work ≤ workBound n s.pool.palette A := by
  have hl := WindowWork.effectiveLower_work_le a.windows v A A (fun u => h.publicRow u v) h.lower
  have hu := WindowWork.effectiveUpper_work_le a.windows v A A (h.publicRow v) h.upper
  unfold pin
  simp only [LocalAccess.cacheWith_eq]
  split
  · rename_i hlow
    have hlow' : s.pool.system.effectiveLower v = c := by
      simpa only [WindowWork.effectiveLower_value, LocalAccess.windows_system] using hlow
    have hcach := LocalAccess.cache_work_le (lowerPromotionAccess a v hv c hlow')
      (lowerPromotionAccess_bound a h v hv c hlow')
    change _ + _ + (lowerPromotionAccess a v hv c hlow').cache.work + 32 ≤ _
    change _ ≤ LocalAccess.cacheBound n (s.pool.palette + 1) (2 * A + 16) at hcach
    unfold workBound
    omega
  · rename_i hlow
    split
    · rename_i hupp
      have hupp' : s.pool.system.effectiveUpper v = c := by
        simpa only [WindowWork.effectiveUpper_value, LocalAccess.windows_system] using hupp
      have hcach := LocalAccess.cache_work_le (upperPromotionAccess a v hv c hupp')
        (upperPromotionAccess_bound a h v hv c hupp')
      change _ + _ + (upperPromotionAccess a v hv c hupp').cache.work + 32 ≤ _
      change _ ≤ LocalAccess.cacheBound n (s.pool.palette + 1) (2 * A + 16) at hcach
      unfold workBound
      omega
    · rename_i hupp
      have hlow' : s.pool.system.effectiveLower v ≠ c := by
        simpa only [WindowWork.effectiveLower_value, LocalAccess.windows_system] using hlow
      have hupp' : s.pool.system.effectiveUpper v ≠ c := by
        simpa only [WindowWork.effectiveUpper_value, LocalAccess.windows_system] using hupp
      have interior : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v :=
        ⟨lt_of_le_of_ne hc.1 hlow', lt_of_le_of_ne hc.2 hupp'.symm⟩
      have hcach := LocalAccess.cache_work_le (interiorPromotionAccess a v hv c interior)
        (interiorPromotionAccess_bound a h v hv c interior)
      have hmono := LocalAccess.cacheBound_mono (n := n) (A := 2 * A + 16)
        (Nat.le_succ s.pool.palette) le_rfl
      change LocalAccess.cacheBound n s.pool.palette (2 * A + 16) ≤
        LocalAccess.cacheBound n (s.pool.palette + 1) (2 * A + 16) at hmono
      change _ ≤ LocalAccess.cacheBound n s.pool.palette (2 * A + 16) at hcach
      change _ + _ + (interiorPromotionAccess a v hv c interior).cache.work + 32 ≤ _
      unfold workBound
      omega

end SortingAdversary.Optimal.MeasuredPin
