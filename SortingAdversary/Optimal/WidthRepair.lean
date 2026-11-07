import SortingAdversary.Optimal.NumericalRepresentation
import SortingAdversary.Optimal.PaletteBirthOrder
import SortingAdversary.Optimal.SeparatedPins
import SortingAdversary.Optimal.ScaleMass

/-!
# Concrete single-pool width repairs

The state carries the actual pool, persistent source-row partition, and
chronological palette permutation. Primitive transitions record the precise
parent promotion or pair of artificial cut walls, for chronological replay
into the recursive tree.
-/

namespace SortingAdversary.Optimal.WidthRepair

open WeakMaps WeakMaps.WeakSystem FiniteRefinement ControllerRouting
open PoolState NumericalRepresentation CutNormalization SparseClosure FiniteInsertion
open SeparatedPins

variable {n : ℕ}

structure State (n : ℕ) where
  pool : Pool n
  rows : SourcePartition pool.system pool.pins
  order : Equiv.Perm (Fin (pool.palette + 1))

namespace State

def width (s : State n) (v : Fin n) : ℕ := CutNormalization.width s.pool.system v

def measure (s : State n) : ℕ :=
  s.pool.free.card + (SparseRepairGraph.rawRows s.rows.active).card

def numerical (s : State n) : OrderedSystem n s.pool.palette :=
  let h := s.rows.view_invariant s.pool.invariant s.pool.pin_bounds
  ⟨closeSystem s.rows.view, h.closed, h.antisymm⟩

theorem numerical_feasible (s : State n) : ∃ f, s.numerical.system.Valid f :=
  (s.rows.view_invariant s.pool.invariant s.pool.pin_bounds).feasible

theorem numerical_width (s : State n) (v : Fin n) :
    windowWidth s.numerical v = s.width v := by
  have hw := s.rows.view_windows s.pool.pin_bounds s.pool.invariant.feasible v
  change ((closeSystem s.rows.view).effectiveUpper v).val + 1 -
    ((closeSystem s.rows.view).effectiveLower v).val = _
  rw [hw.1, hw.2]
  rfl

theorem numerical_count (s : State n) : s.numerical.system.count = s.pool.system.count := by
  change (closeSystem s.rows.view).count = _
  rw [closeSystem_count, s.rows.view_count s.pool.pin_bounds]

theorem numerical_fiber (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1)) :
    s.numerical.system.fiber v c = s.pool.system.fiber v c := by
  change (closeSystem s.rows.view).maps.filter _ = _
  rw [closeSystem_maps, s.rows.view_maps s.pool.pin_bounds]
  rfl

theorem width_pos (s : State n) (v : Fin n) : 0 < s.width v := by
  rw [← s.numerical_width]
  exact windowWidth_pos s.numerical s.numerical_feasible v

theorem active_free (s : State n) {u v : Fin n} (huv : s.rows.active u v = true) :
    s.pool.pins u = none ∧ s.pool.pins v = none := s.rows.active_free u v huv

theorem neighbor_free (s : State n) {v w : Fin n} (hw : w ∈ GraphBalls.neighbors s.rows.active v) :
    s.pool.pins v = none ∧ s.pool.pins w = none := by
  rcases (GraphBalls.mem_neighbors _ _ _).mp hw with ⟨_, hvw | hwv⟩
  · exact s.active_free hvw
  · exact (s.active_free hwv).symm

theorem nonisolated_free (s : State n) {v : Fin n}
    (hv : (GraphBalls.neighbors s.rows.active v).Nonempty) : s.pool.pins v = none := by
  obtain ⟨w, hw⟩ := hv
  exact (s.neighbor_free hw).1

theorem nonisolated_mate (s : State n) {v : Fin n}
    (hv : (GraphBalls.neighbors s.rows.active v).Nonempty) : HasMate s.pool v := by
  obtain ⟨w, hw⟩ := hv
  have hwf := (s.neighbor_free hw).2
  obtain ⟨hne, hvw | hwv⟩ := (GraphBalls.mem_neighbors _ _ _).mp hw
  · exact ⟨w, s.pool.free_member hwf, hne, Or.inl (s.rows.active_public hvw)⟩
  · exact ⟨w, s.pool.free_member hwf, hne, Or.inr (s.rows.active_public hwv)⟩

/-- The concrete graph and chronological dictionary returned with a parent
promotion. The active-row equality supplies its termination charge. -/
structure PromotionData (s : State n) (v : Fin n) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c) where
  rows : SourcePartition r.system r.newPins
  source_eq : rows.source = s.rows.source
  active_eq : rows.active = SparseRepairGraph.eraseVertex s.rows.active v
  order : Equiv.Perm (Fin (r.palette + 1))
  order_old : ∀ i : Fin (s.pool.palette + 1),
    order (Fin.castLE (Nat.succ_le_succ r.palette_bounds.1) i) = r.embed (s.order i)

def promotionData (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    PromotionData s v c
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc) := by
  unfold Promotion.promote
  split
  · refine ⟨s.rows.lowerRepair s.pool.pin_bounds v c, rfl, ?_, PaletteBirthOrder.extendAfter s.order c, ?_⟩
    · change ((s.rows.split s.pool.pin_bounds c).pin v (freshColor c)).active = _
      rw [SourcePartition.pin_active, SourcePartition.split_active]
    · exact fun i => PaletteBirthOrder.extendAfter_old s.order c i
  · split
    · refine ⟨s.rows.upperRepair s.pool.pin_bounds v c, rfl, ?_, PaletteBirthOrder.extendBefore s.order c, ?_⟩
      · change ((s.rows.splitBefore s.pool.pin_bounds c).pin v c.castSucc).active = _
        rw [SourcePartition.pin_active, SourcePartition.splitBefore_active]
      · exact fun i => PaletteBirthOrder.extendBefore_old s.order c i
    · exact ⟨s.rows.pin v c, rfl, SourcePartition.pin_active _ _ _, s.order, fun _ => rfl⟩

def promote (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) : State n :=
  let r := Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc
  let data := s.promotionData v hv c hc
  ⟨s.pool.installPromotion v hv c r, data.rows, data.order⟩

theorem promote_active (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (s.promote v hv c hc).rows.active = SparseRepairGraph.eraseVertex s.rows.active v :=
  (s.promotionData v hv c hc).active_eq

theorem promote_free (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (s.promote v hv c hc).pool.free = s.pool.free.erase v :=
  Pool.installPromotion_free s.pool v hv c
    (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc)

theorem promote_measure_lt (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v) :
    (s.promote v hv c hc).measure < s.measure := by
  unfold measure
  rw [promote_free, promote_active]
  exact Nat.add_lt_add_of_lt_of_le
    (Finset.card_erase_lt_of_mem ((s.pool.free_iff v).mpr hv))
    (SparseRepairGraph.eraseVertex_count_le s.rows.active v)

theorem promote_separated (s : State n) (v : Fin n) (hv : s.pool.pins v = none)
    (c : Fin (s.pool.palette + 1))
    (hc : s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v)
    (hs : Separated s.pool) (hm : HasMate s.pool v) : Separated (s.promote v hv c hc).pool :=
  promotion_separated s.pool v hv c
    (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v hv c hc) hs hm

def lowerCutPool (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width v < s.width u) : Pool n where
  palette := s.pool.palette
  positive := s.pool.positive
  members := s.pool.members
  system := CutNormalization.lowerWidthCut s.pool.system u v
  pins := s.pool.pins
  invariant := lowerWidthCut_invariant s.pool.invariant (s.rows.active_public huv) hratio
  pin_bounds := lowerWidthCut_pinBounds s.pool.invariant s.pool.pin_bounds (s.rows.active_public huv) hratio
  capacity := s.pool.capacity
  outside := by
    intro x hx
    have hu : u ∈ s.pool.members := s.pool.free_member (s.active_free huv).1
    have hv : v ∈ s.pool.members := s.pool.free_member (s.active_free huv).2
    have hxu : x ≠ u := fun h => hx (h ▸ hu)
    have hxv : x ≠ v := fun h => hx (h ▸ hv)
    obtain ⟨hpin, hUnused⟩ := s.pool.outside x hx
    refine ⟨?_, ?_⟩
    · simpa [CutNormalization.lowerWidthCut, floorCut, cut, lowerWall, upperWall, hxv] using hpin
    · refine ⟨rfl, ?_, hUnused.outgoing, hUnused.incoming⟩
      simpa [CutNormalization.lowerWidthCut, floorCut, cut, lowerWall, upperWall, hxv, hxu]
        using hUnused.upper.trans hUnused.lower.symm

def upperCutPool (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width u < s.width v) : Pool n where
  palette := s.pool.palette
  positive := s.pool.positive
  members := s.pool.members
  system := CutNormalization.upperWidthCut s.pool.system u v
  pins := s.pool.pins
  invariant := upperWidthCut_invariant s.pool.invariant (s.rows.active_public huv) hratio
  pin_bounds := upperWidthCut_pinBounds s.pool.invariant s.pool.pin_bounds (s.rows.active_public huv) hratio
  capacity := s.pool.capacity
  outside := by
    intro x hx
    have hu : u ∈ s.pool.members := s.pool.free_member (s.active_free huv).1
    have hv : v ∈ s.pool.members := s.pool.free_member (s.active_free huv).2
    have hxu : x ≠ u := fun h => hx (h ▸ hu)
    have hxv : x ≠ v := fun h => hx (h ▸ hv)
    obtain ⟨hpin, hUnused⟩ := s.pool.outside x hx
    refine ⟨?_, ?_⟩
    · simpa [CutNormalization.upperWidthCut, ceilingCut, cut, lowerWall, upperWall, hxv] using hpin
    · refine ⟨rfl, ?_, hUnused.outgoing, hUnused.incoming⟩
      simpa [CutNormalization.upperWidthCut, ceilingCut, cut, lowerWall, upperWall, hxv, hxu]
        using hUnused.upper.trans hUnused.lower.symm

def lowerCut (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width v < s.width u) : State n :=
  ⟨s.lowerCutPool u v huv hratio,
    s.rows.lowerWidthCut s.pool.invariant.feasible u v (s.rows.active_public huv) hratio, s.order⟩

def upperCut (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width u < s.width v) : State n :=
  ⟨s.upperCutPool u v huv hratio,
    s.rows.upperWidthCut s.pool.invariant.feasible u v (s.rows.active_public huv) hratio, s.order⟩

theorem lowerCut_active (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width v < s.width u) :
    (s.lowerCut u v huv hratio).rows.active = SparseRepairGraph.eraseRow s.rows.active u v :=
  SourcePartition.strictCut_active s.rows u v _ _
    (floor_gap_of_width s.rows.closed s.pool.invariant.feasible (s.rows.active_public huv) hratio).2

theorem upperCut_active (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width u < s.width v) :
    (s.upperCut u v huv hratio).rows.active = SparseRepairGraph.eraseRow s.rows.active u v :=
  SourcePartition.strictCut_active s.rows u v _ _
    (ceiling_gap_of_width s.rows.closed s.pool.invariant.feasible (s.rows.active_public huv) hratio).1

theorem lowerCut_measure_lt (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width v < s.width u) : (s.lowerCut u v huv hratio).measure < s.measure := by
  unfold measure
  rw [lowerCut_active]
  exact Nat.add_lt_add_left (SparseRepairGraph.eraseRow_count_lt s.rows.active
    ⟨s.rows.proper u v (s.rows.active_source u v huv), huv⟩) _

theorem upperCut_measure_lt (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width u < s.width v) : (s.upperCut u v huv hratio).measure < s.measure := by
  unfold measure
  rw [upperCut_active]
  exact Nat.add_lt_add_left (SparseRepairGraph.eraseRow_count_lt s.rows.active
    ⟨s.rows.proper u v (s.rows.active_source u v huv), huv⟩) _

def centralColour (s : State n) (v : Fin n) : Fin (s.pool.palette + 1) :=
  ⟨ScaleMass.intervalLower s.numerical v,
    (ScaleMass.interval_bounds s.numerical s.numerical_feasible v).2.1.trans_le
      (ScaleMass.interval_upper_le s.numerical s.numerical_feasible v)⟩

theorem centralColour_window (s : State n) (v : Fin n) :
    s.pool.system.effectiveLower v ≤ s.centralColour v ∧
      s.centralColour v ≤ s.pool.system.effectiveUpper v := by
  have hb := ScaleMass.interval_bounds s.numerical s.numerical_feasible v
  have hw := s.rows.view_windows s.pool.pin_bounds s.pool.invariant.feasible v
  have h : s.numerical.system.effectiveLower v ≤ s.centralColour v ∧
      s.centralColour v ≤ s.numerical.system.effectiveUpper v := by
    change (s.numerical.system.effectiveLower v).val ≤ ScaleMass.intervalLower s.numerical v ∧
      ScaleMass.intervalLower s.numerical v ≤ (s.numerical.system.effectiveUpper v).val
    omega
  change (closeSystem s.rows.view).effectiveLower v ≤ s.centralColour v ∧
    s.centralColour v ≤ (closeSystem s.rows.view).effectiveUpper v at h
  simpa only [hw.1, hw.2] using h

def cheapPin (s : State n) (v : Fin n)
    (hv : (GraphBalls.neighbors s.rows.active v).Nonempty) : State n :=
  s.promote v (s.nonisolated_free hv) (s.centralColour v) (s.centralColour_window v)

theorem cheapPin_measure_lt (s : State n) (v : Fin n)
    (hv : (GraphBalls.neighbors s.rows.active v).Nonempty) : (s.cheapPin v hv).measure < s.measure :=
  s.promote_measure_lt v (s.nonisolated_free hv) (s.centralColour v) (s.centralColour_window v)

theorem cheapPin_count (s : State n) (v : Fin n)
    (hv : (GraphBalls.neighbors s.rows.active v).Nonempty) (W₀ B : ℕ)
    (hwidth : s.width v ≤ W₀) (hB : comparableCount s.numerical v ≤ B) :
    s.pool.system.count ≤ W₀ * 4 ^ B * (s.cheapPin v hv).pool.system.count := by
  have h0 := ScaleMass.central_count s.numerical s.numerical_feasible v (s.centralColour v)
    ⟨le_rfl, (ScaleMass.interval_bounds s.numerical s.numerical_feasible v).2.1⟩
  have h := h0.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul ((s.numerical_width v).trans_le hwidth)
      (Nat.pow_le_pow_right (by decide : 0 < 4) hB)))
  rw [s.numerical_count, s.numerical_fiber] at h
  exact h.trans (Nat.mul_le_mul_left _
    (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v
      (s.nonisolated_free hv) (s.centralColour v) (s.centralColour_window v)).retains_fiber)

theorem lowerCut_separated (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width v < s.width u) (h : Separated s.pool) :
    Separated (s.lowerCut u v huv hratio).pool := h

theorem upperCut_separated (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width u < s.width v) (h : Separated s.pool) :
    Separated (s.upperCut u v huv hratio).pool := h

theorem numerical_active (s : State n) {u v : Fin n} (huv : s.rows.active u v = true) :
    s.numerical.system.edge u v = true := by
  change (closeSystem s.rows.view).edge u v = true
  simp only [closeSystem, SourcePartition.view, lookup_tableClosure]
  exact closure_old s.rows.active huv

theorem numerical_valid (s : State n) (f : ColorMap (Fin n) (s.pool.palette + 1)) :
    s.numerical.system.Valid f ↔ s.pool.system.Valid f :=
  (closeSystem_valid s.rows.view f).trans (s.rows.view_valid s.pool.pin_bounds f)

theorem lowerCut_retention (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width v < s.width u) (L : ℚ) (hL : 0 < L)
    (hscale : L * (s.width v : ℚ) ≤ s.width u) :
    1 - (2 * 4 ^ comparableCount s.numerical u : ℚ) / L ≤
      ((s.lowerCut u v huv hratio).pool.system.count : ℚ) / s.pool.system.count := by
  have hscale' : L * (CutNormalization.width s.numerical.system v : ℚ) ≤
      CutNormalization.width s.numerical.system u := by
    change L * (windowWidth s.numerical v : ℚ) ≤ windowWidth s.numerical u
    simpa only [s.numerical_width] using hscale
  have h := CutNormalization.lower_retention s.numerical s.numerical_feasible
    (s.numerical_active huv) L hL hscale'
  have hw := (s.rows.view_windows s.pool.pin_bounds s.pool.invariant.feasible v).1
  have heq : (CutNormalization.lowerWidthCut s.numerical.system u v).count =
      (CutNormalization.lowerWidthCut s.pool.system u v).count := by
    unfold CutNormalization.lowerWidthCut floorCut
    change (cut s.numerical.system u v (previousColor ((closeSystem s.rows.view).effectiveLower v))
      ((closeSystem s.rows.view).effectiveLower v)).count = _
    rw [hw]
    exact cut_count_congr s.pool.system s.numerical.system s.numerical_valid u v _ _
  rw [heq, s.numerical_count] at h
  exact h

theorem upperCut_retention (s : State n) (u v : Fin n) (huv : s.rows.active u v = true)
    (hratio : 2 * s.width u < s.width v) (L : ℚ) (hL : 0 < L)
    (hscale : L * (s.width u : ℚ) ≤ s.width v) :
    1 - (2 * 4 ^ comparableCount s.numerical v : ℚ) / L ≤
      ((s.upperCut u v huv hratio).pool.system.count : ℚ) / s.pool.system.count := by
  have hscale' : L * (CutNormalization.width s.numerical.system u : ℚ) ≤
      CutNormalization.width s.numerical.system v := by
    change L * (windowWidth s.numerical u : ℚ) ≤ windowWidth s.numerical v
    simpa only [s.numerical_width] using hscale
  have h := CutNormalization.upper_retention s.numerical s.numerical_feasible
    (s.numerical_active huv) L hL hscale'
  have hw := (s.rows.view_windows s.pool.pin_bounds s.pool.invariant.feasible u).2
  have heq : (CutNormalization.upperWidthCut s.numerical.system u v).count =
      (CutNormalization.upperWidthCut s.pool.system u v).count := by
    unfold CutNormalization.upperWidthCut ceilingCut
    change (cut s.numerical.system u v ((closeSystem s.rows.view).effectiveUpper u)
      (nextColor ((closeSystem s.rows.view).effectiveUpper u))).count = _
    rw [hw]
    exact cut_count_congr s.pool.system s.numerical.system s.numerical_valid u v _ _
  rw [heq, s.numerical_count] at h
  exact h

end State

/-- A replayable physical pin, with its actual parent result and explicit
efficient charge. Full map counts occur only in the proof field. -/
structure PinUpdate (s : State n) where
  vertex : Fin n
  free : s.pool.pins vertex = none
  colour : Fin (s.pool.palette + 1)
  supported : s.pool.system.effectiveLower vertex ≤ colour ∧ colour ≤ s.pool.system.effectiveUpper vertex
  mate : HasMate s.pool vertex
  result : Promotion.Result s.pool.system s.pool.pins vertex colour
  actual : result = Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds
    vertex free colour supported
  data : State.PromotionData s vertex colour result
  charge : ℚ
  retained : (s.pool.system.count : ℚ) ≤ charge * result.system.count

def PinUpdate.next {s : State n} (p : PinUpdate s) : State n :=
  ⟨s.pool.installPromotion p.vertex p.free p.colour p.result, p.data.rows, p.data.order⟩

theorem PinUpdate.measure_lt {s : State n} (p : PinUpdate s) : p.next.measure < s.measure := by
  change (s.pool.installPromotion p.vertex p.free p.colour p.result).free.card +
    (SparseRepairGraph.rawRows p.data.rows.active).card < _
  rw [Pool.installPromotion_free, p.data.active_eq]
  exact Nat.add_lt_add_of_lt_of_le
    (Finset.card_erase_lt_of_mem ((s.pool.free_iff p.vertex).mpr p.free))
    (SparseRepairGraph.eraseVertex_count_le s.rows.active p.vertex)

theorem PinUpdate.separated {s : State n} (p : PinUpdate s) (h : Separated s.pool) :
    Separated p.next.pool := promotion_separated s.pool p.vertex p.free p.colour p.result h p.mate

/-- A primitive parent transition, suitable for chronological tree replay. -/
inductive Step : State n → State n → Type
  | pin {s : State n} (update : PinUpdate s) : Step s update.next
  | lowerCut (s : State n) (u v : Fin n) (live : s.rows.active u v = true)
      (ratio : 2 * s.width v < s.width u) (charge : ℚ)
      (retained : (s.pool.system.count : ℚ) ≤ charge * (s.lowerCut u v live ratio).pool.system.count) :
      Step s (s.lowerCut u v live ratio)
  | upperCut (s : State n) (u v : Fin n) (live : s.rows.active u v = true)
      (ratio : 2 * s.width u < s.width v) (charge : ℚ)
      (retained : (s.pool.system.count : ℚ) ≤ charge * (s.upperCut u v live ratio).pool.system.count) :
      Step s (s.upperCut u v live ratio)

namespace Step

def charge {s t : State n} : Step s t → ℚ
  | .pin p => p.charge
  | .lowerCut _ _ _ _ _ q _ => q
  | .upperCut _ _ _ _ _ q _ => q

theorem retained {s t : State n} (a : Step s t) :
    (s.pool.system.count : ℚ) ≤ a.charge * t.pool.system.count := by
  cases a with
  | pin p => exact p.retained
  | lowerCut _ _ _ _ _ h => exact h
  | upperCut _ _ _ _ _ h => exact h

theorem charge_pos {s t : State n} (a : Step s t) : 0 < a.charge := by
  have hs : (0 : ℚ) < s.pool.system.count := by exact_mod_cast s.pool.count_pos
  have ht : (0 : ℚ) < t.pool.system.count := by exact_mod_cast t.pool.count_pos
  have h := a.retained
  nlinarith

theorem measure_lt {s t : State n} (a : Step s t) : t.measure < s.measure := by
  cases a with
  | pin p => exact p.measure_lt
  | lowerCut u v h r _ _ => exact s.lowerCut_measure_lt u v h r
  | upperCut u v h r _ _ => exact s.upperCut_measure_lt u v h r

theorem public_edges {s t : State n} (a : Step s t) : t.pool.system.edge = s.pool.system.edge := by
  cases a with
  | pin p => exact p.result.edges
  | lowerCut => rfl
  | upperCut => rfl

theorem members {s t : State n} (a : Step s t) : t.pool.members = s.pool.members := by
  cases a <;> rfl

theorem active_old {s t : State n} (a : Step s t) (u v : Fin n)
    (h : t.rows.active u v = true) : s.rows.active u v = true := by
  cases a with
  | pin p =>
    change p.data.rows.active u v = true at h
    rw [p.data.active_eq] at h
    exact SparseRepairGraph.eraseVertex_old s.rows.active p.vertex u v h
  | lowerCut x y live ratio _ _ =>
    rw [State.lowerCut_active] at h
    exact SparseRepairGraph.eraseRow_old s.rows.active x y u v h
  | upperCut x y live ratio _ _ =>
    rw [State.upperCut_active] at h
    exact SparseRepairGraph.eraseRow_old s.rows.active x y u v h

theorem separated {s t : State n} (a : Step s t) (h : Separated s.pool) : Separated t.pool := by
  cases a with
  | pin p => exact p.separated h
  | lowerCut u v live ratio _ _ => exact s.lowerCut_separated u v live ratio h
  | upperCut u v live ratio _ _ => exact s.upperCut_separated u v live ratio h

end Step

/-- Chronological primitive execution, with every intermediate pool fixed by
the preceding certified update. -/
inductive Trace : State n → State n → Type
  | nil (s : State n) : Trace s s
  | cons {s t u : State n} (head : Step s t) (tail : Trace t u) : Trace s u

namespace Trace

def length {s t : State n} : Trace s t → ℕ
  | .nil _ => 0
  | .cons _ rest => rest.length + 1

def charge {s t : State n} : Trace s t → ℚ
  | .nil _ => 1
  | .cons head rest => head.charge * rest.charge

def append {s t u : State n} : Trace s t → Trace t u → Trace s u
  | .nil _, next => next
  | .cons head rest, next => .cons head (rest.append next)

theorem retained {s t : State n} (trace : Trace s t) :
    (s.pool.system.count : ℚ) ≤ trace.charge * t.pool.system.count := by
  induction trace with
  | nil s => simp [charge]
  | @cons s t u head tail ih =>
    exact head.retained.trans (by
      simpa only [charge, mul_assoc] using mul_le_mul_of_nonneg_left ih head.charge_pos.le)

theorem length_add_measure_le {s t : State n} (trace : Trace s t) :
    trace.length + t.measure ≤ s.measure := by
  induction trace with
  | nil s => simp [length]
  | cons head tail ih =>
    have h := head.measure_lt
    change tail.length + 1 + _ ≤ _
    omega

theorem public_edges {s t : State n} (trace : Trace s t) : t.pool.system.edge = s.pool.system.edge := by
  induction trace with
  | nil s => rfl
  | cons head tail ih => exact ih.trans head.public_edges

theorem members {s t : State n} (trace : Trace s t) : t.pool.members = s.pool.members := by
  induction trace with
  | nil s => rfl
  | cons head tail ih => exact ih.trans head.members

theorem separated {s t : State n} (trace : Trace s t) (h : Separated s.pool) : Separated t.pool := by
  induction trace with
  | nil s => exact h
  | cons head tail ih => exact ih (head.separated h)

end Trace

end SortingAdversary.Optimal.WidthRepair
