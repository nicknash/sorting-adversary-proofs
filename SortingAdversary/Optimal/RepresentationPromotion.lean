import SortingAdversary.Optimal.RepresentationCells
import SortingAdversary.Optimal.RepresentationIdentity
import SortingAdversary.Optimal.WidthInterior

/-!
# Measured getters after the actual parent promotion

The endpoint tests are evaluated by measured window scans. Each branch then
constructs its new primitive walls, pins, sparse rows, and both permutation
directions from the previous measured getters.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair FiniteRefinement PoolState
open NumericalRepresentation RefinementTransitions PinTransitions

variable {n : ℕ} {s : State n}

def lowerResult (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hl : s.pool.system.effectiveLower v = c) : Promotion.Result s.pool.system s.pool.pins v c where
  palette := s.pool.palette + 1
  system := lowerRefinement s.pool.system s.pool.pins v c
  newPins := recordPin (mapPins (embedColor c) s.pool.pins) v (freshColor c)
  embed := embedColor c
  destination := freshColor c
  embed_strict := embedColor_strictMono c
  palette_bounds := ⟨Nat.le_succ _, le_rfl⟩
  invariant := lower_refinement_invariant s.pool.invariant s.pool.pin_bounds v c hl
    (hl ▸ s.pool.invariant.free_window v hv)
  pin_bounds := by
    have hi := lower_split_interior s.pool.invariant s.pool.pin_bounds v c hl
      (hl ▸ s.pool.invariant.free_window v hv)
    exact pin_bounds_preserved (split_invariant s.pool.invariant s.pool.pin_bounds c)
      (split_pin_bounds s.pool.system s.pool.pins c) v (freshColor c) hi.1.le hi.2.le
  edges := rfl
  pins_eq := rfl
  retains_fiber := lower_refinement_count s.pool.system s.pool.invariant.closed s.pool.pins
    s.pool.pin_bounds v c s.pool.system.effectiveUpper
    (s.pool.system.effectiveUpper_valid s.pool.invariant.closed
      ((s.pool.system.feasible_iff_windows s.pool.invariant.closed).mp s.pool.invariant.feasible))
    (hl ▸ s.pool.invariant.free_window v hv)
  independent := fun _ d _ hd => False.elim (Promotion.freshColor_ne_embed c d hd.symm)

theorem lowerResult_actual (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hl : s.pool.system.effectiveLower v = c) :
    lowerResult s v hv c hl = Promotion.promote s.pool.system s.pool.pins s.pool.invariant
      s.pool.pin_bounds v hv c hc := by
  unfold Promotion.promote
  rw [dif_pos hl]
  rfl

def lowerData (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hl : s.pool.system.effectiveLower v = c) :
    State.PromotionData s v c (lowerResult s v hv c hl) where
  rows := s.rows.lowerRepair s.pool.pin_bounds v c
  source_eq := rfl
  active_eq := by
    change ((s.rows.split s.pool.pin_bounds c).pin v (freshColor c)).active = _
    rw [SourcePartition.pin_active, SourcePartition.split_active]
  order := PaletteBirthOrder.extendAfter s.order c
  order_old := fun i => PaletteBirthOrder.extendAfter_old s.order c i

def lowerState (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hl : s.pool.system.effectiveLower v = c) : State n :=
  ⟨s.pool.installPromotion v hv c (lowerResult s v hv c hl),
    (lowerData s v hv c hl).rows, (lowerData s v hv c hl).order⟩

theorem stateFromResult_eq_promote (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (r : Promotion.Result s.pool.system s.pool.pins v c)
    (hr : r = Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc)
    (d : State.PromotionData s v c r) :
    (⟨s.pool.installPromotion v hv c r, d.rows, d.order⟩ : State n) = s.promote v hv c hc := by
  cases hr
  have hd := promotionData_unique d (s.promotionData v hv c hc)
  rw [hd]
  rfl

theorem lowerState_actual (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hl : s.pool.system.effectiveLower v = c) : lowerState s v hv c hl = s.promote v hv c hc :=
  stateFromResult_eq_promote s v hv c hc _ (lowerResult_actual s v hv c hc hl) _

def lowerPromotionAccess (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hl : s.pool.system.effectiveLower v = c) :
    LocalAccess (lowerState s v hv c hl) := by
  refine {
    publicRow := a.publicRow
    source := a.source
    active := eraseVertex a.active v
    lower := pinLower (K := s.pool.palette + 1 + 1)
      (splitWall (K := s.pool.palette + 1) (L := s.pool.palette + 1 + 1)
        a.pin a.lower (embedAfter c) (embedAfter c)) v (freshColor c)
    upper := pinUpper (K := s.pool.palette + 1 + 1)
      (splitWall (K := s.pool.palette + 1) (L := s.pool.palette + 1 + 1)
        a.pin a.upper (embedAfter c) (embedUpper c)) v (freshColor c)
    pin := pinMap (K := s.pool.palette + 1) (L := s.pool.palette + 1 + 1)
      a.pin (embedAfter c) v (freshColor c)
    member := a.member
    order := extendForward (K := s.pool.palette + 1) a.order (freshColor c)
    inverse := extendInverse (K := s.pool.palette + 1) a.inverse (freshColor c)
    publicRow_value := a.publicRow_value
    source_value := ?_
    active_value := ?_
    lower_value := ?_
    upper_value := ?_
    pin_value := ?_
    member_value := a.member_value
    order_value := ?_
    inverse_value := ?_ }
  · intro x y
    exact a.source_value x y
  · intro x y
    exact (eraseVertex_value a v x y).trans
      (congrArg (fun r => r x y) (lowerData s v hv c hl).active_eq).symm
  · intro x
    simp only [lowerState, lowerResult, pinLower, splitWall, a.pin_value, a.lower_value, embedAfter,
      Pool.installPromotion, lowerRefinement, pinAt, splitPalette]
    cases s.pool.pins x <;> rfl
  · intro x
    simp only [lowerState, lowerResult, pinUpper, splitWall, a.pin_value, a.upper_value, embedAfter, embedUpper,
      Pool.installPromotion, lowerRefinement, pinAt, splitPalette]
    cases s.pool.pins x <;> rfl
  · intro x
    by_cases hx : x = v <;> cases hp : s.pool.pins x <;>
      simp [lowerState, lowerResult, pinMap, a.pin_value, embedAfter, recordPin, mapPins, hx, hp, Pool.installPromotion]
  · exact extendForward_value s.order a.order a.order_value (freshColor c)
  · exact extendInverse_value s.order a.inverse a.inverse_value (freshColor c)

def upperResult (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hu : s.pool.system.effectiveUpper v = c) :
    Promotion.Result s.pool.system s.pool.pins v c where
  palette := s.pool.palette + 1
  system := upperRefinement s.pool.system s.pool.pins v c
  newPins := recordPin (mapPins (embedColorBefore c) s.pool.pins) v c.castSucc
  embed := embedColorBefore c
  destination := c.castSucc
  embed_strict := embedColorBefore_strictMono c
  palette_bounds := ⟨Nat.le_succ _, le_rfl⟩
  invariant := upper_refinement_invariant s.pool.invariant s.pool.pin_bounds v c
    (hu ▸ s.pool.invariant.free_window v hv) hu
  pin_bounds := by
    have hi := upper_split_interior s.pool.invariant s.pool.pin_bounds v c
      (hu ▸ s.pool.invariant.free_window v hv) hu
    exact pin_bounds_preserved (splitBefore_invariant s.pool.invariant s.pool.pin_bounds c)
      (splitBefore_pin_bounds s.pool.system s.pool.pins c) v c.castSucc hi.1.le hi.2.le
  edges := rfl
  pins_eq := rfl
  retains_fiber := upper_refinement_count s.pool.system s.pool.invariant.closed s.pool.pins
    s.pool.pin_bounds v c s.pool.system.effectiveLower
    (s.pool.system.effectiveLower_valid s.pool.invariant.closed
      ((s.pool.system.feasible_iff_windows s.pool.invariant.closed).mp s.pool.invariant.feasible))
    (hu ▸ s.pool.invariant.free_window v hv)
  independent := fun _ d _ hd => False.elim (Promotion.beforeColor_ne_embed c d hd.symm)

theorem upperResult_actual (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hl : s.pool.system.effectiveLower v ≠ c) (hu : s.pool.system.effectiveUpper v = c) :
    upperResult s v hv c hu = Promotion.promote s.pool.system s.pool.pins s.pool.invariant
      s.pool.pin_bounds v hv c hc := by
  unfold Promotion.promote
  rw [dif_neg hl, dif_pos hu]
  rfl

def upperData (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hu : s.pool.system.effectiveUpper v = c) :
    State.PromotionData s v c (upperResult s v hv c hu) where
  rows := s.rows.upperRepair s.pool.pin_bounds v c
  source_eq := rfl
  active_eq := by
    change ((s.rows.splitBefore s.pool.pin_bounds c).pin v c.castSucc).active = _
    rw [SourcePartition.pin_active, SourcePartition.splitBefore_active]
  order := PaletteBirthOrder.extendBefore s.order c
  order_old := fun i => PaletteBirthOrder.extendBefore_old s.order c i

def upperState (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hu : s.pool.system.effectiveUpper v = c) : State n :=
  ⟨s.pool.installPromotion v hv c (upperResult s v hv c hu),
    (upperData s v hv c hu).rows, (upperData s v hv c hu).order⟩

theorem upperState_actual (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hl : s.pool.system.effectiveLower v ≠ c) (hu : s.pool.system.effectiveUpper v = c) :
    upperState s v hv c hu = s.promote v hv c hc :=
  stateFromResult_eq_promote s v hv c hc _ (upperResult_actual s v hv c hc hl hu) _

def upperPromotionAccess (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1)) (hu : s.pool.system.effectiveUpper v = c) :
    LocalAccess (upperState s v hv c hu) := by
  refine {
    publicRow := a.publicRow
    source := a.source
    active := eraseVertex a.active v
    lower := pinLower (K := s.pool.palette + 1 + 1)
      (splitWall (K := s.pool.palette + 1) (L := s.pool.palette + 1 + 1)
        a.pin a.lower (embedBefore c) (embedAfter c)) v c.castSucc
    upper := pinUpper (K := s.pool.palette + 1 + 1)
      (splitWall (K := s.pool.palette + 1) (L := s.pool.palette + 1 + 1)
        a.pin a.upper (embedBefore c) (embedUpper c)) v c.castSucc
    pin := pinMap (K := s.pool.palette + 1) (L := s.pool.palette + 1 + 1)
      a.pin (embedBefore c) v c.castSucc
    member := a.member
    order := extendForward (K := s.pool.palette + 1) a.order c.castSucc
    inverse := extendInverse (K := s.pool.palette + 1) a.inverse c.castSucc
    publicRow_value := a.publicRow_value
    source_value := a.source_value
    active_value := ?_
    lower_value := ?_
    upper_value := ?_
    pin_value := ?_
    member_value := a.member_value
    order_value := ?_
    inverse_value := ?_ }
  · intro x y
    exact (eraseVertex_value a v x y).trans
      (congrArg (fun r => r x y) (upperData s v hv c hu).active_eq).symm
  · intro x
    simp only [upperState, upperResult, pinLower, splitWall, a.pin_value, a.lower_value,
      embedAfter, embedBefore, Pool.installPromotion, upperRefinement, pinAt, splitPaletteBefore]
    cases s.pool.pins x <;> rfl
  · intro x
    simp only [upperState, upperResult, pinUpper, splitWall, a.pin_value, a.upper_value,
      embedBefore, embedUpper, Pool.installPromotion, upperRefinement, pinAt, splitPaletteBefore]
    cases s.pool.pins x <;> rfl
  · intro x
    by_cases hx : x = v <;> cases hp : s.pool.pins x <;>
      simp [upperState, upperResult, pinMap, a.pin_value, embedBefore, recordPin, mapPins, hx, hp,
        Pool.installPromotion]
  · exact extendForward_value s.order a.order a.order_value c.castSucc
  · exact extendInverse_value s.order a.inverse a.inverse_value c.castSucc

def interiorData (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    State.PromotionData s v c (s.interiorResult v c hc) where
  rows := s.rows.pin v c
  source_eq := rfl
  active_eq := SourcePartition.pin_active _ _ _
  order := s.order
  order_old := fun _ => rfl

def interiorState (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) : State n :=
  ⟨s.pool.installPromotion v hv c (s.interiorResult v c hc),
    (interiorData s v c hc).rows, s.order⟩

theorem interiorState_actual (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    interiorState s v hv c hc = s.promote v hv c ⟨hc.1.le, hc.2.le⟩ :=
  stateFromResult_eq_promote s v hv c _ _ (s.interiorResult_actual v hv c hc) (interiorData s v c hc)

def interiorPromotionAccess (a : LocalAccess s) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v < c ∧ c < s.pool.system.effectiveUpper v) :
    LocalAccess (interiorState s v hv c hc) where
  publicRow := a.publicRow
  source := a.source
  active := eraseVertex a.active v
  lower := pinLower (K := s.pool.palette + 1) a.lower v c
  upper := pinUpper (K := s.pool.palette + 1) a.upper v c
  pin := pinMap (K := s.pool.palette + 1) (L := s.pool.palette + 1)
    a.pin (fun c => ⟨c, 0⟩) v c
  member := a.member
  order := a.order
  inverse := a.inverse
  publicRow_value := a.publicRow_value
  source_value := a.source_value
  active_value x y := (eraseVertex_value a v x y).trans
    (congrArg (fun r => r x y) (interiorData s v c hc).active_eq).symm
  lower_value x := by simp only [pinLower, a.lower_value]; rfl
  upper_value x := by simp only [pinUpper, a.upper_value]; rfl
  pin_value x := by
    by_cases hx : x = v <;> cases hp : s.pool.pins x <;>
      simp [interiorState, State.interiorResult, pinMap, a.pin_value, recordPin, hx, hp,
        Pool.installPromotion]
  member_value := a.member_value
  order_value := a.order_value
  inverse_value := a.inverse_value

end SortingAdversary.Optimal.RepresentationWork
