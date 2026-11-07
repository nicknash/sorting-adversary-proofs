import SortingAdversary.Optimal.WidthInterior
import SortingAdversary.Optimal.LocalOracle
import SortingAdversary.Optimal.HubPricing

/-!
# Executable ordinary calibrated promotions

Wide calibrated intervals use the actual trimmed dyadic hub selector. A
short interval uses an actual singleton block. If the selected endpoint
forces a palette split, its historical record is the newborn destination's
singleton after that split, rather than the old pre-split color identity.
-/

namespace SortingAdversary.Optimal.OrdinaryPromotion

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState LocalOracle IsolatedAccuracy
open StableBatches HubSelector BatchWindows MarginalCalibration FiniteRefinement
open SeparatedPins

variable {n K : ℕ}

/-- Trim a wide interval, or retain only its first color when it is short. -/
def inputWindow (a b : Fin (K + 1)) : ℕ × ℕ :=
  if 8 ≤ b.val + 1 - a.val then (a.val + 1, b.val) else (a.val, a.val + 1)

theorem inputWindow_bounds (a b : Fin (K + 1)) (hab : a ≤ b) :
    a.val ≤ (inputWindow a b).1 ∧ (inputWindow a b).1 < (inputWindow a b).2 ∧
      (inputWindow a b).2 ≤ b.val + 1 ∧ (inputWindow a b).2 ≤ K + 1 := by
  unfold inputWindow
  split_ifs <;> have ha := a.isLt <;> have hb := b.isLt <;> change a.val ≤ b.val at hab <;> simp only <;> omega

/-- Deterministic extraction from the proved successful finite selector.
The impossibility proof for `none` is erased, not used as a choice function. -/
def selectNonempty (order : Equiv.Perm (Fin (K + 1))) (lower upper : ℕ)
    (hupper : upper ≤ K + 1) (hroom : lower < upper) :
    {a : Block // selectWindow order lower upper ∅ = some a} :=
  match hsel : selectWindow order lower upper ∅ with
  | some a => ⟨a, rfl⟩
  | none => False.elim (by
      obtain ⟨a, ha⟩ := selectWindow_exists (lower := lower) (upper := upper) order ∅ hupper (by
        simp only [vetoCost, Finset.sum_empty]
        omega)
      rw [hsel] at ha
      contradiction)

/-- The actual selected dyadic record for the current calibrated interval. -/
def intervalBlock (order : Equiv.Perm (Fin (K + 1))) (a b : Fin (K + 1)) (hab : a ≤ b) :
    {chosen : Block // selectWindow order (inputWindow a b).1 (inputWindow a b).2 ∅ = some chosen} :=
  selectNonempty order _ _ (inputWindow_bounds a b hab).2.2.2 (inputWindow_bounds a b hab).2.1

theorem intervalBlock_available (order : Equiv.Perm (Fin (K + 1)))
    (a b : Fin (K + 1)) (hab : a ≤ b) :
    (intervalBlock order a b hab).val ∈ allBlocks (K + 1) :=
  (selected_spec (intervalBlock order a b hab).property).1

def intervalColour (order : Equiv.Perm (Fin (K + 1))) (a b : Fin (K + 1)) (hab : a ≤ b) :
    Fin (K + 1) :=
  ⟨paletteRank order (hubColour (paletteRank order) (paletteRank_injective order)
      (intervalBlock order a b hab).val),
    (selected_hub_in_window order (intervalBlock order a b hab).property).2.trans_le
      (inputWindow_bounds a b hab).2.2.2⟩

theorem intervalColour_mem (order : Equiv.Perm (Fin (K + 1)))
    (a b : Fin (K + 1)) (hab : a ≤ b) :
    a ≤ intervalColour order a b hab ∧ intervalColour order a b hab ≤ b := by
  have h := selected_hub_in_window order (intervalBlock order a b hab).property
  have hw := inputWindow_bounds a b hab
  change a.val ≤ _ ∧ _ ≤ b.val
  dsimp only [intervalColour]
  omega

theorem intervalColour_interior (order : Equiv.Perm (Fin (K + 1)))
    (a b : Fin (K + 1)) (hab : a ≤ b) (hlarge : 8 ≤ b.val + 1 - a.val) :
    a < intervalColour order a b hab ∧ intervalColour order a b hab < b := by
  have h := selected_hub_in_window order (intervalBlock order a b hab).property
  simp only [inputWindow, if_pos hlarge] at h
  change a.val < _ ∧ _ < b.val
  dsimp only [intervalColour]
  omega

theorem intervalBlock_short_size (order : Equiv.Perm (Fin (K + 1)))
    (a b : Fin (K + 1)) (hab : a ≤ b) (hsmall : ¬8 ≤ b.val + 1 - a.val) :
    (intervalBlock order a b hab).val.size = 1 := by
  have hsel := (intervalBlock order a b hab).property
  simp only [inputWindow, if_neg hsmall] at hsel
  have hs := ScaleHubs.selected_size_le_window order (by have := a.isLt; omega) hsel
  have hp := (intervalBlock order a b hab).val.size_pos
  omega

theorem hub_identity_bound (order : Equiv.Perm (Fin (K + 1))) {chosen : Block}
    (ha : chosen ∈ allBlocks (K + 1)) :
    hubColour (paletteRank order) (paletteRank_injective order) chosen < K + 1 := by
  obtain ⟨hb, hfits⟩ := (mem_allBlocks _ _).mp ha
  exact (currentBatches_cover _ _).mp
    ⟨chosen.batch, hb, hubColour_mem (paletteRank order) (paletteRank_injective order) hfits⟩

/-- The selected current rank identifies its immutable old color exactly. -/
theorem intervalColour_identity (order : Equiv.Perm (Fin (K + 1)))
    (a b : Fin (K + 1)) (hab : a ≤ b) :
    (order.symm (intervalColour order a b hab)).val =
      hubColour (paletteRank order) (paletteRank_injective order) (intervalBlock order a b hab).val := by
  let c := hubColour (paletteRank order) (paletteRank_injective order) (intervalBlock order a b hab).val
  have hc : c < K + 1 := hub_identity_bound order (intervalBlock_available order a b hab)
  have heq : intervalColour order a b hab = order ⟨c, hc⟩ := by
    apply Fin.ext
    exact paletteRank_apply order ⟨c, hc⟩
  rw [heq, Equiv.symm_apply_apply]

theorem support_of_count (S : WeakSystem (Fin n) (K + 1)) (hS : 0 < S.count)
    (v : Fin n) (c : Fin (K + 1)) (A : ℕ)
    (h : S.count ≤ A * (S.fiber v c).card) : ∃ f, S.Valid f ∧ f v = c := by
  have hpos : 0 < (S.fiber v c).card := by
    by_contra hz
    have hz' : (S.fiber v c).card = 0 := by omega
    rw [hz', Nat.mul_zero] at h
    omega
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
  exact ⟨f, (S.mem_fiber v c f).mp hf⟩

/-- The computed calibrated interval, actual selector record and true-parent
count guarantee. No probability conclusion is an input to the constructor. -/
structure Choice (s : State n) (v : Fin n) where
  lower : Fin (s.pool.palette + 1)
  upper : Fin (s.pool.palette + 1)
  ordered : lower ≤ upper
  block : Block
  selected : selectWindow s.order (inputWindow lower upper).1 (inputWindow lower upper).2 ∅ = some block
  colour : Fin (s.pool.palette + 1)
  rank_eq : colour.val = paletteRank s.order (hubColour (paletteRank s.order) (paletteRank_injective s.order) block)
  in_interval : lower ≤ colour ∧ colour ≤ upper
  supported : s.pool.system.effectiveLower v ≤ colour ∧ colour ≤ s.pool.system.effectiveUpper v
  count : s.pool.system.count ≤ 16 * (upper.val + 1 - lower.val) * (s.pool.system.fiber v colour).card
  interior : 8 ≤ upper.val + 1 - lower.val →
    s.pool.system.effectiveLower v < colour ∧ colour < s.pool.system.effectiveUpper v

set_option maxHeartbeats 2000000 in
def choose (s : State n) (H d : ℕ) (g : SparseBounds s.rows H d) (R : ℚ) (hR : 0 ≤ R)
    (v : Fin n) (hv : MarkCondition s.rows.view H d R (1 / 16) v) : Choice s v := by
  let I := calibrationInterval s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv
  have hI := calibration_mass s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv
  have hord : I.1 ≤ I.2 := hI.1
  let chosen := intervalBlock s.order I.1 I.2 hord
  let c := intervalColour s.order I.1 I.2 hord
  have hc : I.1 ≤ c ∧ c ≤ I.2 := intervalColour_mem s.order I.1 I.2 hord
  have hcount : s.pool.system.count ≤ 16 * (I.2.val + 1 - I.1.val) *
      (s.pool.system.fiber v c).card :=
    calibration_fiber_count s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv c hc.1 hc.2
  have hsupport := support_of_count s.pool.system s.pool.count_pos v c _ hcount
  have hwindow := (s.pool.system.support_iff_window s.pool.invariant.closed
    s.pool.invariant.feasible v c).mp hsupport
  refine
    { lower := I.1
      upper := I.2
      ordered := hord
      block := chosen.val
      selected := chosen.property
      colour := c
      rank_eq := rfl
      in_interval := hc
      supported := hwindow
      count := hcount
      interior := ?_ }
  intro hlarge
  have hlcount := calibration_fiber_count s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv
    I.1 le_rfl hord
  have hucount := calibration_fiber_count s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv
    I.2 hord le_rfl
  have hl := (s.pool.system.support_iff_window s.pool.invariant.closed s.pool.invariant.feasible v I.1).mp
    (support_of_count s.pool.system s.pool.count_pos v I.1 _ hlcount)
  have hu := (s.pool.system.support_iff_window s.pool.invariant.closed s.pool.invariant.feasible v I.2).mp
    (support_of_count s.pool.system s.pool.count_pos v I.2 _ hucount)
  have hc' := intervalColour_interior s.order I.1 I.2 hord hlarge
  exact ⟨hl.1.trans_lt hc'.1, hc'.2.trans_le hu.2⟩

namespace Choice

variable {s : State n} {v : Fin n}

def width (c : Choice s v) : ℕ := c.upper.val + 1 - c.lower.val

theorem width_pos (c : Choice s v) : 0 < c.width := by
  have h : c.lower.val ≤ c.upper.val := c.ordered
  unfold width
  omega

theorem available (c : Choice s v) : c.block ∈ allBlocks (s.pool.palette + 1) :=
  (selected_spec c.selected).1

theorem identity (c : Choice s v) :
    (s.order.symm c.colour).val = hubColour (paletteRank s.order) (paletteRank_injective s.order) c.block := by
  let id := hubColour (paletteRank s.order) (paletteRank_injective s.order) c.block
  have hid : id < s.pool.palette + 1 := hub_identity_bound s.order c.available
  have heq : c.colour = s.order ⟨id, hid⟩ := by
    apply Fin.ext
    exact c.rank_eq.trans (paletteRank_apply s.order ⟨id, hid⟩)
  rw [heq, Equiv.symm_apply_apply]

/-- The real parent transition, including endpoint refinement when required. -/
def toPin (c : Choice s v) (hv : s.pool.pins v = none) (hm : HasMate s.pool v) : PinUpdate s where
  vertex := v
  free := hv
  colour := c.colour
  supported := c.supported
  mate := hm
  result := Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c.colour c.supported
  actual := rfl
  data := s.promotionData v hv c.colour c.supported
  charge := 16 * c.width
  retained := by
    have h := Promotion.price_preserved s.pool.system s.pool.pins v c.colour
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c.colour c.supported)
      (16 * c.width) c.count
    exact_mod_cast h

theorem interior_destination (c : Choice s v) (hv : s.pool.pins v = none) (hm : HasMate s.pool v)
    (hlarge : 8 ≤ c.width) :
    ((c.toPin hv hm).data.order.symm (c.toPin hv hm).result.destination).val =
      (s.order.symm c.colour).val := by
  have hembed : (c.toPin hv hm).result.embed c.colour = (c.toPin hv hm).result.destination := by
    have h := s.interiorResult_actual v hv c.colour (c.interior hlarge)
    exact (congrArg (fun r : Promotion.Result s.pool.system s.pool.pins v c.colour =>
      r.embed c.colour = r.destination) h).mp rfl
  have ho := (c.toPin hv hm).data.order_old (s.order.symm c.colour)
  rw [Equiv.apply_symm_apply, hembed] at ho
  have hinv := congrArg (c.toPin hv hm).data.order.symm ho
  simp only [Equiv.symm_apply_apply] at hinv
  exact (congrArg Fin.val hinv).symm

theorem wide_tariff (c : Choice s v) (hlarge : 8 ≤ c.width) (M : ℕ)
    (hcap : s.pool.palette + 1 ≤ 2 ^ M) :
    16 * c.width ≤ 128 * c.block.size * (M - c.block.level + 2) := by
  change 8 ≤ c.upper.val + 1 - c.lower.val at hlarge
  have hsel : selectWindow s.order (c.lower.val + 1) ((c.upper.val + 1) - 1) ∅ = some c.block := by
    simpa only [inputWindow, if_pos hlarge, Nat.add_sub_cancel] using c.selected
  have hupper : c.upper.val + 1 ≤ s.pool.palette + 1 := c.upper.isLt
  have h := selected_trimmed_window_bound s.order hcap hupper hlarge (by simp [vetoCost]) hsel
  calc
    _ ≤ 16 * (8 * c.block.size * (M - c.block.level + 2)) := Nat.mul_le_mul_left 16 h
    _ = _ := by ring

end Choice

/-- The actual singleton selector at a specified current palette rank. -/
def singletonBlock (order : Equiv.Perm (Fin (K + 1))) (destination : Fin (K + 1)) :
    {a : Block // selectWindow order destination.val (destination.val + 1) ∅ = some a} :=
  selectNonempty order _ _ destination.isLt (Nat.lt_succ_self _)

theorem singletonBlock_available (order : Equiv.Perm (Fin (K + 1))) (destination : Fin (K + 1)) :
    (singletonBlock order destination).val ∈ allBlocks (K + 1) :=
  (selected_spec (singletonBlock order destination).property).1

theorem singletonBlock_size (order : Equiv.Perm (Fin (K + 1))) (destination : Fin (K + 1)) :
    (singletonBlock order destination).val.size = 1 := by
  have h := ScaleHubs.selected_size_le_window order destination.isLt (singletonBlock order destination).property
  have hp := (singletonBlock order destination).val.size_pos
  omega

theorem singletonBlock_identity (order : Equiv.Perm (Fin (K + 1))) (destination : Fin (K + 1)) :
    hubColour (paletteRank order) (paletteRank_injective order) (singletonBlock order destination).val =
      (order.symm destination).val := by
  let id := hubColour (paletteRank order) (paletteRank_injective order) (singletonBlock order destination).val
  have hid : id < K + 1 := hub_identity_bound order (singletonBlock_available order destination)
  have hwin := selected_hub_in_window order (singletonBlock order destination).property
  change destination.val ≤ paletteRank order id ∧ paletteRank order id < destination.val + 1 at hwin
  have hrank : paletteRank order id = destination.val := by omega
  have heq : order ⟨id, hid⟩ = destination := by
    apply Fin.ext
    exact (paletteRank_apply order ⟨id, hid⟩).symm.trans hrank
  have hinv := congrArg order.symm heq
  simp only [Equiv.symm_apply_apply] at hinv
  exact congrArg Fin.val hinv

/-- A physical palette extension preserves the relative order of every pair
of already born immutable identities. -/
theorem promotion_rank_preserved {s : State n} (update : PinUpdate s)
    (a b : ℕ) (ha : a < s.pool.palette + 1) (hb : b < s.pool.palette + 1) :
    paletteRank s.order a ≤ paletteRank s.order b ↔
      paletteRank update.data.order a ≤ paletteRank update.data.order b := by
  have haNew : paletteRank update.data.order a =
      (update.result.embed (s.order ⟨a, ha⟩)).val :=
    (paletteRank_apply update.data.order
      (Fin.castLE (Nat.succ_le_succ update.result.palette_bounds.1) ⟨a, ha⟩)).trans
      (congrArg Fin.val (update.data.order_old ⟨a, ha⟩))
  have hbNew : paletteRank update.data.order b =
      (update.result.embed (s.order ⟨b, hb⟩)).val :=
    (paletteRank_apply update.data.order
      (Fin.castLE (Nat.succ_le_succ update.result.palette_bounds.1) ⟨b, hb⟩)).trans
      (congrArg Fin.val (update.data.order_old ⟨b, hb⟩))
  rw [haNew, hbNew, paletteRank_apply s.order ⟨a, ha⟩, paletteRank_apply s.order ⟨b, hb⟩]
  exact update.result.embed_strict.le_iff_le.symm

/-- The historical immutable block used to pay for one actual promotion.
Its destination is the result's true new color identity, including a newborn
identity in either endpoint-refinement branch. -/
structure HubRecord {s : State n} (update : PinUpdate s) where
  births : ℕ
  order : Equiv.Perm (Fin births)
  block : Block
  available : block ∈ allBlocks births
  destination : hubColour (paletteRank order) (paletteRank_injective order) block =
    (update.data.order.symm update.result.destination).val
  born : births ≤ update.result.palette + 1
  orderPreserved : ∀ a b, a < births → b < births →
    (paletteRank order a ≤ paletteRank order b ↔
      paletteRank update.data.order a ≤ paletteRank update.data.order b)
  tariff : ∀ M, births ≤ 2 ^ M →
    update.charge ≤ (128 * block.size * (M - block.level + 2) : ℕ)

namespace Choice

variable {s : State n} {v : Fin n}

/-- Wide choices keep their real old block. Short choices select a singleton
at the post-transition destination, so an endpoint split records its newly
born color and never accidentally charges the pre-split representative. -/
def record (c : Choice s v) (hv : s.pool.pins v = none) (hm : HasMate s.pool v) :
    HubRecord (c.toPin hv hm) :=
  if hlarge : 8 ≤ c.width then
    { births := s.pool.palette + 1
      order := s.order
      block := c.block
      available := c.available
      destination := c.identity.symm.trans (c.interior_destination hv hm hlarge).symm
      born := Nat.succ_le_succ (c.toPin hv hm).result.palette_bounds.1
      orderPreserved := promotion_rank_preserved (c.toPin hv hm)
      tariff := by
        intro M hM
        have h := c.wide_tariff hlarge M hM
        change (16 : ℚ) * (c.width : ℚ) ≤ _
        exact_mod_cast h }
  else
    let chosen := singletonBlock (c.toPin hv hm).data.order (c.toPin hv hm).result.destination
    { births := (c.toPin hv hm).result.palette + 1
      order := (c.toPin hv hm).data.order
      block := chosen.val
      available := singletonBlock_available _ _
      destination := singletonBlock_identity _ _
      born := le_rfl
      orderPreserved := fun _ _ _ _ => Iff.rfl
      tariff := by
        intro M _
        have hs : chosen.val.size = 1 := singletonBlock_size _ _
        have h : 16 * c.width ≤ 128 * chosen.val.size * (M - chosen.val.level + 2) := by
          rw [hs]
          omega
        change (16 : ℚ) * (c.width : ℚ) ≤ _
        exact_mod_cast h }

end Choice

/-- A complete ordinary move, its concrete transition and historical price. -/
structure Move (s : State n) where
  update : PinUpdate s
  record : HubRecord update

def make (s : State n) (H d : ℕ) (g : SparseBounds s.rows H d) (R : ℚ) (hR : 0 ≤ R)
    (v : Fin n) (hmark : MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v) : Move s :=
  let c := choose s H d g R hR v hmark
  ⟨c.toPin hv hm, c.record hv hm⟩

@[simp] theorem make_vertex (s : State n) (H d : ℕ) (g : SparseBounds s.rows H d) (R : ℚ) (hR : 0 ≤ R)
    (v : Fin n) (hmark : MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v) :
    (make s H d g R hR v hmark hv hm).update.vertex = v := rfl

end SortingAdversary.Optimal.OrdinaryPromotion
