import SortingAdversary.Optimal.StructuralNormalize
import SortingAdversary.Optimal.ScaleGroupPrice

/-!
# Actual emitted repair histories and their prices

Historical records retain immutable color identities across every palette
birth. Their decoders are transported to the final order by the actual
promotion embeddings. The concrete event executors supply the chronological
ordinary and scale records used by the largest-block signed-price theorem.
-/

namespace SortingAdversary.Optimal.RepairPricing

open scoped BigOperators
open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState StructuralNormalize
open StableBatches HubSelector BatchWindows HubPricing OrdinaryPromotion

variable {n : ℕ}

/-- Relative order of every already born identity is retained. -/
structure OrderExtension (s t : State n) : Prop where
  births : s.pool.palette + 1 ≤ t.pool.palette + 1
  ranks : ∀ a b, a < s.pool.palette + 1 → b < s.pool.palette + 1 →
    (paletteRank s.order a ≤ paletteRank s.order b ↔ paletteRank t.order a ≤ paletteRank t.order b)

theorem step_order {s t : State n} (step : Step s t) : OrderExtension s t := by
  cases step with
  | pin update => exact ⟨Nat.succ_le_succ update.result.palette_bounds.1,
      promotion_rank_preserved update⟩
  | lowerCut => exact ⟨le_rfl, fun _ _ _ _ => Iff.rfl⟩
  | upperCut => exact ⟨le_rfl, fun _ _ _ _ => Iff.rfl⟩

theorem trace_order {s t : State n} (trace : Trace s t) : OrderExtension s t := by
  induction trace with
  | nil => exact ⟨le_rfl, fun _ _ _ _ => Iff.rfl⟩
  | cons head tail ih =>
    have hs := step_order head
    exact ⟨hs.births.trans ih.births, fun a b ha hb =>
      (hs.ranks a b ha hb).trans (ih.ranks a b (ha.trans_le hs.births) (hb.trans_le hs.births))⟩

/-- A physical pin's color expressed as its immutable birth identity. -/
def ImmutablePin (s : State n) (v : Fin n) (identity : ℕ) : Prop :=
  ∃ c, s.pool.pins v = some c ∧ (s.order.symm c).val = identity

theorem immutablePin_not_free {s : State n} {v : Fin n} {identity : ℕ}
    (h : ImmutablePin s v identity) : v ∉ s.pool.free := by
  obtain ⟨c, hc, _⟩ := h
  intro hf
  rw [(s.pool.free_iff v).mp hf] at hc
  contradiction

theorem step_pin_preserved {s t : State n} (step : Step s t) {v : Fin n} {identity : ℕ}
    (h : ImmutablePin s v identity) : ImmutablePin t v identity := by
  obtain ⟨c, hc, hid⟩ := h
  cases step with
  | pin update =>
    have hv : v ≠ update.vertex := by
      intro heq
      rw [heq, update.free] at hc
      contradiction
    refine ⟨update.result.embed c, ?_, ?_⟩
    · change update.result.newPins v = _
      rw [Promotion.other_pin s.pool.system s.pool.pins update.vertex update.colour update.result hv, hc]
      rfl
    · have ho := update.data.order_old (s.order.symm c)
      rw [Equiv.apply_symm_apply] at ho
      have he := congrArg update.data.order.symm ho
      simp only [Equiv.symm_apply_apply] at he
      exact (congrArg Fin.val he).symm.trans hid
  | lowerCut => exact ⟨c, hc, hid⟩
  | upperCut => exact ⟨c, hc, hid⟩

theorem trace_pin_preserved {s t : State n} (trace : Trace s t) {v : Fin n} {identity : ℕ}
    (h : ImmutablePin s v identity) : ImmutablePin t v identity := by
  induction trace with
  | nil => exact h
  | cons head tail ih => exact ih (step_pin_preserved head h)

theorem interior_embed_value {s : State n} (update : PinUpdate s)
    (hc : s.pool.system.effectiveLower update.vertex < update.colour ∧
      update.colour < s.pool.system.effectiveUpper update.vertex) :
    ∀ a, (update.result.embed a).val = a.val := by
  have hr := (s.interiorResult_actual update.vertex update.free update.colour hc).trans update.actual.symm
  exact (congrArg (fun r : Promotion.Result s.pool.system s.pool.pins update.vertex update.colour =>
    ∀ a, (r.embed a).val = a.val) hr).mp (fun _ => rfl)

theorem interior_rank_eq {s : State n} (update : PinUpdate s)
    (hc : s.pool.system.effectiveLower update.vertex < update.colour ∧
      update.colour < s.pool.system.effectiveUpper update.vertex)
    (a : ℕ) (ha : a < s.pool.palette + 1) :
    paletteRank update.data.order a = paletteRank s.order a := by
  calc
    _ = (update.data.order (Fin.castLE (Nat.succ_le_succ update.result.palette_bounds.1) ⟨a, ha⟩)).val :=
      paletteRank_apply update.data.order _
    _ = (update.result.embed (s.order ⟨a, ha⟩)).val := congrArg Fin.val (update.data.order_old ⟨a, ha⟩)
    _ = (s.order ⟨a, ha⟩).val := interior_embed_value update hc _
    _ = _ := (paletteRank_apply s.order ⟨a, ha⟩).symm

theorem interior_destination {s : State n} (update : PinUpdate s)
    (hc : s.pool.system.effectiveLower update.vertex < update.colour ∧
      update.colour < s.pool.system.effectiveUpper update.vertex) :
    (update.data.order.symm update.result.destination).val = (s.order.symm update.colour).val := by
  have hr := (s.interiorResult_actual update.vertex update.free update.colour hc).trans update.actual.symm
  have he : update.result.embed update.colour = update.result.destination :=
    (congrArg (fun r : Promotion.Result s.pool.system s.pool.pins update.vertex update.colour =>
      r.embed update.colour = r.destination) hr).mp rfl
  have ho := update.data.order_old (s.order.symm update.colour)
  rw [Equiv.apply_symm_apply, he] at ho
  have hi := congrArg update.data.order.symm ho
  simp only [Equiv.symm_apply_apply] at hi
  exact (congrArg Fin.val hi).symm

/-- An actual historical hub record, with an explicit ordinary/scale tag. -/
structure HubEvent (n : ℕ) where
  vertex : Fin n
  scale : Bool
  births : ℕ
  order : Equiv.Perm (Fin births)
  block : Block
  available : block ∈ allBlocks births
  identity : ℕ
  selected : hubColour (paletteRank order) (paletteRank_injective order) block = identity

namespace HubEvent

variable {event : HubEvent n}

def ordinary {s : State n} (move : OrdinaryPromotion.Move s) : HubEvent n where
  vertex := move.update.vertex
  scale := false
  births := move.record.births
  order := move.record.order
  block := move.record.block
  available := move.record.available
  identity := (move.update.data.order.symm move.update.result.destination).val
  selected := move.record.destination

/-- A historical record is linked to the actual final physical pin, and its
entire old dictionary order is preserved in that final state. -/
structure Fits (event : HubEvent n) (s : State n) : Prop where
  births : event.births ≤ s.pool.palette + 1
  ranks : ∀ a b, a < event.births → b < event.births →
    (paletteRank event.order a ≤ paletteRank event.order b ↔ paletteRank s.order a ≤ paletteRank s.order b)
  pinned : ImmutablePin s event.vertex event.identity
  member : event.vertex ∈ s.pool.members

theorem ordinary_fits {s : State n} (move : OrdinaryPromotion.Move s) :
    (ordinary move).Fits move.update.next :=
  ⟨move.record.born, move.record.orderPreserved,
    ⟨move.update.result.destination, Promotion.promoted_pin _ _ _ _ _, rfl⟩,
    s.pool.free_member move.update.free⟩

theorem Fits.advance {s t : State n} (h : event.Fits s) (trace : Trace s t) : event.Fits t := by
  have ho := trace_order trace
  exact ⟨h.births.trans ho.births, fun a b ha hb =>
    (h.ranks a b ha hb).trans (ho.ranks a b (ha.trans_le h.births) (hb.trans_le h.births)),
    trace_pin_preserved trace h.pinned, trace.members.symm ▸ h.member⟩

theorem member_lt (event : HubEvent n) {a : ℕ} (ha : a ∈ event.block.batch.members) : a < event.births :=
  (currentBatches_cover _ _).mp
    ⟨event.block.batch, ((mem_allBlocks _ _).mp event.available).1, ha⟩

theorem Fits.decoder {s : State n} (h : event.Fits s) :
    hubColour (paletteRank s.order) (paletteRank_injective s.order) event.block = event.identity := by
  have he := hubColour_stable (paletteRank event.order) (paletteRank s.order)
    (paletteRank_injective event.order) (paletteRank_injective s.order) event.block
    (fun a ha b hb => h.ranks a b (event.member_lt ha) (event.member_lt hb))
  exact he.symm.trans event.selected

def past (event : HubEvent n) (M : ℕ) (hcap : event.births ≤ 2 ^ M) : PastBlock M :=
  ⟨event.births, hcap, event.block, event.available⟩

@[simp] theorem Fits.decode_past {s : State n} (h : event.Fits s)
    (M : ℕ) (hcap : s.pool.palette + 1 ≤ 2 ^ M) :
    decodeColour (paletteRank s.order) (paletteRank_injective s.order)
      (encode (event.past M (h.births.trans hcap))) = event.identity := by
  rw [decodeColour_encode]
  exact h.decoder

noncomputable def unitPrice (M : ℕ) (event : HubEvent n) : ℝ :=
  Real.log ((128 : ℝ) * event.block.size * (M - event.block.level + 2 : ℕ))

noncomputable def price (p : Parameters) (M : ℕ) (event : HubEvent n) : ℝ :=
  event.unitPrice M + if event.scale then Real.log (2 * (4 : ℝ) ^ p.scale.width.B) else 0

end HubEvent

end SortingAdversary.Optimal.RepairPricing

namespace SortingAdversary.Optimal.RepairPricing

open scoped BigOperators
open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState StructuralNormalize
open StableBatches HubSelector BatchWindows HubPricing OrdinaryPromotion

variable {n : ℕ}

theorem trace_charge_pos {s t : State n} (trace : Trace s t) : 0 < trace.charge := by
  induction trace with
  | nil => exact zero_lt_one
  | cons head tail ih => exact mul_pos head.charge_pos ih

theorem trace_charge_append {s t u : State n} (first : Trace s t) (second : Trace t u) :
    (first.append second).charge = first.charge * second.charge := by
  induction first with
  | nil => simp [Trace.append, Trace.charge]
  | cons head tail ih => simp only [Trace.append, Trace.charge, ih, mul_assoc]

theorem trace_length_append {s t u : State n} (first : Trace s t) (second : Trace t u) :
    (first.append second).length = first.length + second.length := by
  induction first with
  | nil => simp [Trace.append, Trace.length]
  | cons head tail ih => simp only [Trace.append, Trace.length, ih]; omega

noncomputable def logCharge {s t : State n} (trace : Trace s t) : ℝ := Real.log (trace.charge : ℝ)

theorem logCharge_append {s t u : State n} (first : Trace s t) (second : Trace t u) :
    logCharge (first.append second) = logCharge first + logCharge second := by
  unfold logCharge
  rw [trace_charge_append, Rat.cast_mul, Real.log_mul]
  · exact_mod_cast (trace_charge_pos first).ne'
  · exact_mod_cast (trace_charge_pos second).ne'

noncomputable def totalPrice (p : Parameters) (M cheap cuts : ℕ) (hubs : List (HubEvent n)) : ℝ :=
  cheap * Real.log (p.scale.width.cheapCharge : ℝ) + cuts * Real.log (p.scale.width.cutCharge : ℝ) +
    (hubs.map (HubEvent.price p M)).sum

/-- A finite history extracted from actual typed execution. All hub records
are linked to their final physical pin, and the whole trace pays their
explicit prices plus only the actual cheap pins and cuts. -/
structure Summary (p : Parameters) {s t : State n} (trace : Trace s t) where
  hubs : List (HubEvent n)
  cheap : ℕ
  cuts : ℕ
  fits : ∀ e ∈ hubs, e.Fits t
  fresh : ∀ e ∈ hubs, e.vertex ∈ s.pool.free
  nodup : (hubs.map HubEvent.vertex).Nodup
  accounted : hubs.length + cheap + cuts = trace.length
  priced : ∀ M, t.pool.palette + 1 ≤ 2 ^ M →
    logCharge trace ≤ totalPrice p M cheap cuts hubs

namespace Summary

variable {p : Parameters} {s t u : State n} {first : Trace s t} {second : Trace t u}

def empty (s : State n) (p : Parameters) : Summary p (.nil s) :=
  ⟨[], 0, 0, by simp, by simp, by simp, rfl, by intro M hM; simp [logCharge, Trace.charge, totalPrice]⟩

def append (left : Summary p first) (right : Summary p second) : Summary p (first.append second) where
  hubs := left.hubs ++ right.hubs
  cheap := left.cheap + right.cheap
  cuts := left.cuts + right.cuts
  fits := by
    intro e he
    rcases List.mem_append.mp he with hl | hr
    · exact (left.fits e hl).advance second
    · exact right.fits e hr
  fresh := by
    intro e he
    rcases List.mem_append.mp he with hl | hr
    · exact left.fresh e hl
    · exact first.free_subset (right.fresh e hr)
  nodup := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨left.nodup, right.nodup, ?_⟩
    intro a ha b hb hab
    obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
    obtain ⟨eb, heb, rfl⟩ := List.mem_map.mp hb
    apply immutablePin_not_free (left.fits ea hea).pinned
    rw [hab]
    exact right.fresh eb heb
  accounted := by
    have hl := left.accounted
    have hr := right.accounted
    have ht := trace_length_append first second
    simp only [List.length_append]
    omega
  priced := by
    intro M hM
    have hl := left.priced M ((trace_order second).births.trans hM)
    have hr := right.priced M hM
    rw [logCharge_append]
    unfold totalPrice at hl hr ⊢
    simp only [Nat.cast_add, List.map_append, List.sum_append]
    nlinarith

/-- The retained fraction proof is already attached to the actual primitive
pin. This constructor only inserts its real dictionary record in history. -/
def oneHub (p : Parameters) (update : PinUpdate s) (event : HubEvent n)
    (hvertex : event.vertex = update.vertex) (hfits : event.Fits update.next)
    (hprice : ∀ M, update.next.pool.palette + 1 ≤ 2 ^ M →
      Real.log (update.charge : ℝ) ≤ event.price p M) :
    Summary p (.cons (.pin update) (.nil update.next)) where
  hubs := [event]
  cheap := 0
  cuts := 0
  fits := by
    intro e he
    have heq : e = event := List.mem_singleton.mp he
    subst e
    exact hfits
  fresh := by
    intro e he
    have heq : e = event := List.mem_singleton.mp he
    subst e
    rw [hvertex]
    exact (s.pool.free_iff _).mpr update.free
  nodup := by simp
  accounted := rfl
  priced := by
    intro M hM
    simpa [logCharge, Trace.charge, Step.charge, totalPrice] using hprice M hM

def ordinary (p : Parameters) (move : OrdinaryPromotion.Move s) :
    Summary p (.cons (.pin move.update) (.nil move.update.next)) :=
  oneHub p move.update (HubEvent.ordinary move) rfl (HubEvent.ordinary_fits move) (by
    intro M hM
    have hprice := move.record.tariff M (move.record.born.trans hM)
    have hreal : (move.update.charge : ℝ) ≤
        (128 * move.record.block.size * (M - move.record.block.level + 2) : ℕ) := by exact_mod_cast hprice
    have hpos : (0 : ℝ) < move.update.charge := by exact_mod_cast (Step.pin move.update).charge_pos
    have hlog := Real.log_le_log hpos hreal
    simpa only [HubEvent.price, HubEvent.unitPrice, HubEvent.ordinary, Bool.false_eq_true,
      if_false, add_zero, Nat.cast_mul, Nat.cast_ofNat] using hlog)

end Summary

/-- Numerical ranks do not move at all during a group of interior scale pins. -/
structure ScaleView (start current : State n) : Prop where
  palette : current.pool.palette = start.pool.palette
  ranks : ∀ a, a < start.pool.palette + 1 → paletteRank current.order a = paletteRank start.order a

namespace ScaleView

variable {start current : State n}

theorem refl (s : State n) : ScaleView s s := ⟨rfl, fun _ _ => rfl⟩

theorem advance (view : ScaleView start current) (update : PinUpdate current)
    (hc : current.pool.system.effectiveLower update.vertex < update.colour ∧
      update.colour < current.pool.system.effectiveUpper update.vertex)
    (hpalette : update.result.palette = current.pool.palette) : ScaleView start update.next := by
  refine ⟨hpalette.trans view.palette, ?_⟩
  intro a ha
  have ha' : a < current.pool.palette + 1 := by rwa [view.palette]
  exact (interior_rank_eq update hc a ha').trans (view.ranks a ha)

end ScaleView

theorem block_available {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) :
    trigger.block normal i ∈ allBlocks (s.pool.palette + 1) :=
  selectGroup_mem_allBlocks _ _ _ _ _ _ (List.getElem_mem _)

def scaleEvent {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) : HubEvent n where
  vertex := trigger.vertices i
  scale := true
  births := s.pool.palette + 1
  order := s.order
  block := trigger.block normal i
  available := block_available trigger normal i
  identity := hubColour (paletteRank s.order) (paletteRank_injective s.order) (trigger.block normal i)
  selected := rfl

theorem scaleEvent_fits {start current : State n} {p : ScaleParameters}
    (trigger : ScaleTrigger start p) (normal : EarlyNormal start p.width.W₀ p.width.L)
    (view : ScaleView start current) (i : Fin p.J) (update : PinUpdate current)
    (hvertex : update.vertex = trigger.vertices i)
    (hcolour : update.colour.val = (trigger.colour normal i).val)
    (hc : current.pool.system.effectiveLower update.vertex < update.colour ∧
      update.colour < current.pool.system.effectiveUpper update.vertex) :
    (scaleEvent trigger normal i).Fits update.next := by
  have hborn : start.pool.palette + 1 ≤ update.result.palette + 1 := by
    rw [← view.palette]
    exact Nat.succ_le_succ update.result.palette_bounds.1
  refine ⟨hborn, ?_, ?_, ?_⟩
  · intro a b ha hb
    have ha' : a < current.pool.palette + 1 := by rwa [view.palette]
    have hb' : b < current.pool.palette + 1 := by rwa [view.palette]
    change paletteRank start.order a ≤ paletteRank start.order b ↔
      paletteRank update.data.order a ≤ paletteRank update.data.order b
    rw [interior_rank_eq update hc a ha', interior_rank_eq update hc b hb',
      view.ranks a ha, view.ranks b hb]
  · refine ⟨update.result.destination, ?_, ?_⟩
    · change update.result.newPins (trigger.vertices i) = _
      rw [← hvertex]
      exact Promotion.promoted_pin _ _ _ _ _
    · change (update.data.order.symm update.result.destination).val = _
      rw [interior_destination update hc]
      let identity := (scaleEvent trigger normal i).identity
      have hid : identity < start.pool.palette + 1 := hub_identity_bound start.order (block_available trigger normal i)
      have hid' : identity < current.pool.palette + 1 := by rwa [view.palette]
      have hrank : paletteRank current.order identity = update.colour.val := by
        rw [view.ranks identity hid, hcolour]
        rfl
      have heq : current.order ⟨identity, hid'⟩ = update.colour := by
        apply Fin.ext
        exact (paletteRank_apply current.order ⟨identity, hid'⟩).symm.trans hrank
      rw [← heq, Equiv.symm_apply_apply]
  · change trigger.vertices i ∈ current.pool.members
    rw [← hvertex]
    exact current.pool.free_member update.free

end SortingAdversary.Optimal.RepairPricing

namespace SortingAdversary.Optimal.RepairPricing.Summary

open scoped BigOperators
open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState StructuralNormalize
open StableBatches HubSelector BatchWindows HubPricing OrdinaryPromotion

variable {n : ℕ}

/-- The scale insertion charge is the ordinary block tariff plus its explicit
`2 * 4^B` multiplicative surcharge, with the actual accumulated veto paid. -/
def scaleOne (p : Parameters) {start current : State n} (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    (view : ScaleView start current) (i : Fin p.scale.J) (update : PinUpdate current)
    (hvertex : update.vertex = trigger.vertices i)
    (hcolour : update.colour.val = (trigger.colour normal i).val)
    (hc : current.pool.system.effectiveLower update.vertex < update.colour ∧
      update.colour < current.pool.system.effectiveUpper update.vertex)
    (hcharge : update.charge = (2 * 4 ^ p.scale.width.B * (trigger.upper i.val - trigger.lower i.val) : ℕ)) :
    Summary p (.cons (.pin update) (.nil update.next)) :=
  oneHub p update (scaleEvent trigger normal i) hvertex.symm
    (scaleEvent_fits trigger normal view i update hvertex hcolour hc) (by
      intro M hM
      have hstart : start.pool.palette + 1 ≤ 2 ^ M := by
        rw [← view.palette]
        exact (Nat.succ_le_succ update.result.palette_bounds.1).trans hM
      have hm := trigger.block_price normal M hstart i
      let factor := 2 * 4 ^ p.scale.width.B
      let block := trigger.block normal i
      have hnat : factor * (trigger.upper i.val - trigger.lower i.val) ≤
          128 * block.size * (M - block.level + 2) * factor := by
        calc
          _ ≤ factor * (8 * block.size * (M - block.level + 2)) := Nat.mul_le_mul_left factor hm
          _ ≤ factor * (128 * block.size * (M - block.level + 2)) := Nat.mul_le_mul_left factor
            (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 8 ≤ 128)))
          _ = _ := by ring
      have hreal : (update.charge : ℝ) ≤
          ((128 : ℝ) * block.size * (M - block.level + 2 : ℕ)) * (2 * (4 : ℝ) ^ p.scale.width.B) := by
        rw [hcharge]
        exact_mod_cast hnat
      have hp : (0 : ℝ) < update.charge := by exact_mod_cast (Step.pin update).charge_pos
      have hb : (0 : ℝ) < block.size := by exact_mod_cast block.size_pos
      have hslack : (0 : ℝ) < (M - block.level + 2 : ℕ) := by exact_mod_cast (by omega : 0 < M - block.level + 2)
      have hh := Real.log_le_log hp hreal
      rw [Real.log_mul (by positivity) (by positivity)] at hh
      exact hh)

/-- A cheap pin or a cut has no dictionary record and retains its precise
kind-specific scalar charge from the actual width executor. -/
def oneNonHub (p : Parameters) {s t : State n} (step : Step s t) (cheap : Bool)
    (hcharge : step.charge = if cheap then p.scale.width.cheapCharge else p.scale.width.cutCharge) :
    Summary p (.cons step (.nil t)) where
  hubs := []
  cheap := if cheap then 1 else 0
  cuts := if cheap then 0 else 1
  fits := by simp
  fresh := by simp
  nodup := by simp
  accounted := by cases cheap <;> rfl
  priced := by
    intro M hM
    cases cheap <;> simp [logCharge, Trace.charge, totalPrice, hcharge]

def oneEarly (p : Parameters) {s : State n} (hB : ComparableBound s p.scale.width.B)
    (move : EarlyMove s p.scale.width.W₀ p.scale.width.L) :
    Summary p (.cons (move.execute p.scale.width hB).2 (.nil (move.execute p.scale.width hB).1)) := by
  cases move with
  | cheap v incident narrow => exact oneNonHub p _ true rfl
  | lower u v live steep => exact oneNonHub p _ false rfl
  | upper u v live steep => exact oneNonHub p _ false rfl

def fromEarly (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p.scale.width trace) : Summary p trace :=
  match events with
  | .nil s => empty s p
  | .cons hB move rest events => (oneEarly p hB move).append (fromEarly p events)

def fromScale (p : Parameters) (start : State n) (trigger : ScaleTrigger start p.scale)
    (normal : EarlyNormal start p.scale.width.W₀ p.scale.width.L)
    {s t : State n} {trace : Trace s t} {indices : List (Fin p.scale.J)}
    (events : ScaleEvents start p.scale trigger normal trace indices) (view : ScaleView start s) :
    Summary p trace :=
  match events with
  | .nil s => empty s p
  | .cons i update vertex colour interior palette charge rest events =>
    (scaleOne p trigger normal view i update vertex colour interior charge).append
      (fromScale p start trigger normal events (view.advance update interior palette))

def fromWidth (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : WidthEvents p.scale trace) : Summary p trace :=
  match events with
  | .early _ events => fromEarly p events
  | .scale _ early trigger _ normal _ group _ rest =>
    (fromEarly p early).append
      ((fromScale p _ trigger normal group (ScaleView.refl _)).append (fromWidth p rest))

def fromPath (p : Parameters) (start : State n) (reservation : Reservation start p.H)
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : Summary p trace :=
  match events with
  | .nil s => empty s p
  | .skip _ _ _ width _ _ rest => (fromWidth p width).append (fromPath p start reservation rest)
  | .move _ _ _ width move _ _ rest =>
    (fromWidth p width).append ((ordinary p move).append (fromPath p start reservation rest))

/-- The actual full controller emits this history. The constructor traverses
its dependent execution certificate and invents no records or pin kinds. -/
def fromEvents (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) : Summary p trace :=
  match events with
  | .finish _ width _ => fromWidth p width
  | .degree _ width move _ _ rest =>
    (fromWidth p width).append ((ordinary p move).append (fromEvents p rest))
  | .path _ width _ reservation _ group _ _ rest =>
    (fromWidth p width).append ((fromPath p _ reservation group).append (fromEvents p rest))

theorem hub_count_le_free {p : Parameters} {s t : State n} {trace : Trace s t}
    (summary : Summary p trace) : summary.hubs.length ≤ s.pool.free.card := by
  have hsub : (summary.hubs.map HubEvent.vertex).toFinset ⊆ s.pool.free := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact summary.fresh e he
  have h := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup summary.nodup, List.length_map] at h
  exact h

/-- Every actual returned hub retains its immutable physical destination in
the final pool, after all later endpoint births and all width repairs. -/
theorem fromEvents_decoder (p : Parameters) {s t : State n} {trace : Trace s t}
    (events : Events p trace) (e : HubEvent n) (he : e ∈ (fromEvents p events).hubs) :
    hubColour (paletteRank t.order) (paletteRank_injective t.order) e.block = e.identity ∧
      ImmutablePin t e.vertex e.identity :=
  ⟨((fromEvents p events).fits e he).decoder, ((fromEvents p events).fits e he).pinned⟩

end SortingAdversary.Optimal.RepairPricing.Summary
