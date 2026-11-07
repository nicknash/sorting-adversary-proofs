import SortingAdversary.Optimal.RepairPricing

/-!
# Actual destination multiplicities of reserved groups

An old physical pin excludes its immutable child identity from every later
promotion of a comparable free label. This is proved from the actual
promotion's independence certificate, including both endpoint births. Every
original reserved path therefore has distinct destinations throughout the
real repair trace, even when intervening cleanup moves its labels.
-/

namespace SortingAdversary.Optimal.RepairPricing

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState StructuralNormalize SeparatedPins
open StableBatches HubSelector BatchWindows

variable {n : ℕ}

def destination (s : State n) (v : Fin n) : Option ℕ :=
  (s.pool.pins v).map (fun c => (s.order.symm c).val)

theorem destination_iff {s : State n} {v : Fin n} {identity : ℕ} :
    destination s v = some identity ↔ ImmutablePin s v identity := by
  simp only [destination, Option.map_eq_some_iff, ImmutablePin]

theorem immutablePin_unique {s : State n} {v : Fin n} {a b : ℕ}
    (ha : ImmutablePin s v a) (hb : ImmutablePin s v b) : a = b := by
  exact Option.some.inj ((destination_iff.mpr ha).symm.trans (destination_iff.mpr hb))

theorem embed_identity {s : State n} (update : PinUpdate s) (c : Fin (s.pool.palette + 1)) :
    (update.data.order.symm (update.result.embed c)).val = (s.order.symm c).val := by
  have ho := update.data.order_old (s.order.symm c)
  rw [Equiv.apply_symm_apply] at ho
  have hi := congrArg update.data.order.symm ho
  simp only [Equiv.symm_apply_apply] at hi
  exact (congrArg Fin.val hi).symm

/-- Absence of a specified immutable child identity, allowing other pins. -/
def Excludes (s : State n) (v : Fin n) (identity : ℕ) : Prop :=
  ∀ c, s.pool.pins v = some c → (s.order.symm c).val ≠ identity

theorem excludes_of_free {s : State n} {v : Fin n} (hv : v ∈ s.pool.free) (identity : ℕ) :
    Excludes s v identity := by
  intro c hc
  rw [(s.pool.free_iff v).mp hv] at hc
  contradiction

theorem excludes_pin_false {s : State n} {v : Fin n} {identity : ℕ}
    (he : Excludes s v identity) (hp : ImmutablePin s v identity) : False := by
  obtain ⟨c, hc, hid⟩ := hp
  exact he c hc hid

theorem step_excludes {s t : State n} (step : Step s t) {x y : Fin n} {identity : ℕ}
    (hx : ImmutablePin s x identity) (hxy : Comparable s.pool x y) (hy : Excludes s y identity) :
    Excludes t y identity := by
  obtain ⟨cx, hcx, hidx⟩ := hx
  cases step with
  | pin update =>
    intro cy hcy hidy
    by_cases hyv : y = update.vertex
    · subst y
      have hdest : update.result.destination = cy := by
        have hnew := Promotion.promoted_pin s.pool.system s.pool.pins update.vertex update.colour update.result
        change update.result.newPins update.vertex = some cy at hcy
        exact Option.some.inj (hnew.symm.trans hcy)
      have heq : update.result.embed cx = update.result.destination := by
        apply update.data.order.symm.injective
        apply Fin.ext
        calc
          _ = identity := (embed_identity update cx).trans hidx
          _ = (update.data.order.symm cy).val := hidy.symm
          _ = _ := congrArg (fun z => (update.data.order.symm z).val) hdest.symm
      exact new_pin_ne_old s.pool update.vertex update.colour update.result hcx hxy.symm heq
    · change update.result.newPins y = some cy at hcy
      rw [Promotion.other_pin s.pool.system s.pool.pins update.vertex update.colour update.result hyv] at hcy
      obtain ⟨c, hold, heq⟩ := Option.map_eq_some_iff.mp hcy
      have hi : (s.order.symm c).val = identity := by
        calc
          _ = (update.data.order.symm (update.result.embed c)).val := (embed_identity update c).symm
          _ = (update.data.order.symm cy).val := congrArg (fun z => (update.data.order.symm z).val) heq
          _ = identity := hidy
      exact hy c hold hi
  | lowerCut => exact hy
  | upperCut => exact hy

theorem trace_excludes {s t : State n} (trace : Trace s t) {x y : Fin n} {identity : ℕ}
    (hx : ImmutablePin s x identity) (hxy : Comparable s.pool x y) (hy : Excludes s y identity) :
    Excludes t y identity := by
  induction trace with
  | nil => exact hy
  | cons head tail ih =>
    apply ih (step_pin_preserved head hx)
    · simpa only [Comparable, head.public_edges] using hxy
    · exact step_excludes head hx hxy hy

/-- Once one member of a comparable pair has moved, the later free member
cannot enter its child, regardless of palette births and numeric cuts. -/
theorem pin_then_distinct {s t : State n} (update : PinUpdate s) (tail : Trace update.next t)
    {y : Fin n} (hy : y ∈ s.pool.free) (hne : y ≠ update.vertex)
    (hcomp : Comparable s.pool update.vertex y) (identity : ℕ)
    (hxFinal : ImmutablePin t update.vertex identity) (hyFinal : ImmutablePin t y identity) : False := by
  let born := (update.data.order.symm update.result.destination).val
  have hx : ImmutablePin update.next update.vertex born :=
    ⟨update.result.destination, Promotion.promoted_pin _ _ _ _ _, rfl⟩
  have hyNew : y ∈ update.next.pool.free := by
    change y ∈ (s.pool.installPromotion update.vertex update.free update.colour update.result).free
    rw [Pool.installPromotion_free]
    exact Finset.mem_erase.mpr ⟨hne, hy⟩
  have hcompNew : Comparable update.next.pool update.vertex y := by
    simpa only [Comparable, PinUpdate.next, Pool.installPromotion, update.result.edges] using hcomp
  have hex := trace_excludes tail hx hcompNew (excludes_of_free hyNew born)
  have hid : identity = born := immutablePin_unique hxFinal (trace_pin_preserved tail hx)
  exact excludes_pin_false hex (hid ▸ hyFinal)

/-- Every comparable pair that is free at the beginning of a real repair
trace has different immutable destinations whenever both have moved. -/
theorem trace_fresh_distinct {s t : State n} (trace : Trace s t) :
    ∀ x y, x ∈ s.pool.free → y ∈ s.pool.free → x ≠ y → Comparable s.pool x y →
      ∀ identity, ImmutablePin t x identity → ImmutablePin t y identity → False := by
  induction trace with
  | nil =>
    intro x y hx hy hne hcomp identity hpin _
    exact immutablePin_not_free hpin hx
  | @cons s a t head tail ih =>
    intro x y hx hy hne hcomp identity hpinx hpiny
    cases head with
    | pin update =>
      by_cases hxv : x = update.vertex
      · subst x
        exact pin_then_distinct update tail hy hne.symm hcomp identity hpinx hpiny
      · by_cases hyv : y = update.vertex
        · subst y
          exact pin_then_distinct update tail hx hxv hcomp.symm identity hpiny hpinx
        · apply ih x y ?_ ?_ hne ?_ identity hpinx hpiny
          · change x ∈ (s.pool.installPromotion update.vertex update.free update.colour update.result).free
            rw [Pool.installPromotion_free]
            exact Finset.mem_erase.mpr ⟨hxv, hx⟩
          · change y ∈ (s.pool.installPromotion update.vertex update.free update.colour update.result).free
            rw [Pool.installPromotion_free]
            exact Finset.mem_erase.mpr ⟨hyv, hy⟩
          · simpa only [Comparable, PinUpdate.next, Pool.installPromotion, update.result.edges] using hcomp
    | lowerCut => exact ih x y hx hy hne hcomp identity hpinx hpiny
    | upperCut => exact ih x y hx hy hne hcomp identity hpinx hpiny

theorem reservation_comparable {s : State n} {H : ℕ} (r : Reservation s H)
    {x y : Fin n} (hx : x ∈ r.labels) (hy : y ∈ r.labels) (hne : x ≠ y) :
    Comparable s.pool x y := by
  letI : Std.Symm (Comparable s.pool) := ⟨fun _ _ h => h.symm⟩
  have hp : r.labels.Pairwise (Comparable s.pool) := r.public_order.imp (fun h => Or.inr h)
  exact hp.forall hx hy hne

/-- Every real reserved path has destination multiplicity at most one,
including labels promoted by intervening cheap or scale cleanup. -/
theorem reservation_destination_multiplicity {s t : State n} {H : ℕ}
    (r : Reservation s H) (hH : 2 ≤ H) (trace : Trace s t) (identity : ℕ) :
    (r.labels.toFinset.filter (fun v => destination t v = some identity)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxm, hxd⟩ := Finset.mem_filter.mp hx
  obtain ⟨hym, hyd⟩ := Finset.mem_filter.mp hy
  have hxl := List.mem_toFinset.mp hxm
  have hyl := List.mem_toFinset.mp hym
  by_contra hne
  exact trace_fresh_distinct trace x y (r.free hH hxl) (r.free hH hyl) hne
    (reservation_comparable r hxl hyl hne) identity (destination_iff.mp hxd) (destination_iff.mp hyd)

end SortingAdversary.Optimal.RepairPricing
