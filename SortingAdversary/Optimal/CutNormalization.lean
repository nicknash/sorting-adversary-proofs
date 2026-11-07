import SortingAdversary.Optimal.PinTransitions
import SortingAdversary.Optimal.FiniteInsertion

/-!
# Strict-wall normalization cuts

The public closed relation is retained.  A cut intersects two primitive unary
lists with explicit walls; effective windows remain derived quantities.
Retiring the corresponding numerical row is a separate, exactly equivalent
representation once these walls imply that row.  This distinction is needed
when a later palette refinement lifts the primitive lists.
-/

namespace SortingAdversary.Optimal.CutNormalization

open WeakMaps WeakMaps.WeakSystem ControllerRouting FiniteRefinement
open PinTransitions Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- Add a primitive upper wall at one coordinate. -/
def upperWall (S : WeakSystem α K) (v : α) (c : Fin K) : WeakSystem α K where
  edge := S.edge
  lower := S.lower
  upper x := if x = v then min (S.upper x) c else S.upper x

/-- Add a primitive lower wall at one coordinate. -/
def lowerWall (S : WeakSystem α K) (v : α) (c : Fin K) : WeakSystem α K where
  edge := S.edge
  lower x := if x = v then max (S.lower x) c else S.lower x
  upper := S.upper

omit [Fintype α] in
@[simp] theorem valid_upperWall (S : WeakSystem α K) (v : α) (c : Fin K)
    (f : ColorMap α K) : (upperWall S v c).Valid f ↔ S.Valid f ∧ f v ≤ c := by
  constructor
  · intro hf
    have hv : f v ≤ min (S.upper v) c := by simpa [upperWall] using (hf.1 v).2
    refine ⟨⟨?_, hf.2⟩, hv.trans (min_le_right _ _)⟩
    intro x
    by_cases hx : x = v
    · subst x
      exact ⟨(hf.1 v).1, hv.trans (min_le_left _ _)⟩
    · simpa [upperWall, hx] using hf.1 x
  · rintro ⟨hf, hc⟩
    refine ⟨?_, hf.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      simpa [upperWall] using ⟨(hf.1 v).1, (hf.1 v).2, hc⟩
    · simpa [upperWall, hx] using hf.1 x

omit [Fintype α] in
@[simp] theorem valid_lowerWall (S : WeakSystem α K) (v : α) (c : Fin K)
    (f : ColorMap α K) : (lowerWall S v c).Valid f ↔ S.Valid f ∧ c ≤ f v := by
  constructor
  · intro hf
    have hv : max (S.lower v) c ≤ f v := by simpa [lowerWall] using (hf.1 v).1
    refine ⟨⟨?_, hf.2⟩, (le_max_right _ _).trans hv⟩
    intro x
    by_cases hx : x = v
    · subst x
      exact ⟨(le_max_left _ _).trans hv, (hf.1 v).2⟩
    · simpa [lowerWall, hx] using hf.1 x
  · rintro ⟨hf, hc⟩
    refine ⟨?_, hf.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      simpa [lowerWall] using ⟨⟨(hf.1 v).1, hc⟩, (hf.1 v).2⟩
    · simpa [lowerWall, hx] using hf.1 x

@[simp] theorem upperWall_lower (S : WeakSystem α (K + 1)) (v x : α) (c : Fin (K + 1)) :
    (upperWall S v c).effectiveLower x = S.effectiveLower x := rfl

@[simp] theorem lowerWall_upper (S : WeakSystem α (K + 1)) (v x : α) (c : Fin (K + 1)) :
    (lowerWall S v c).effectiveUpper x = S.effectiveUpper x := rfl

theorem upperWall_upper (S : WeakSystem α (K + 1)) (v x : α) (c : Fin (K + 1)) :
    (upperWall S v c).effectiveUpper x =
      if S.edge x v = true then min (S.effectiveUpper x) c else S.effectiveUpper x := by
  change (pinAt S v c).effectiveUpper x = _
  exact pinAt_upper S v x c

theorem lowerWall_lower (S : WeakSystem α (K + 1)) (v x : α) (c : Fin (K + 1)) :
    (lowerWall S v c).effectiveLower x =
      if S.edge v x = true then max (S.effectiveLower x) c else S.effectiveLower x := by
  change (pinAt S v c).effectiveLower x = _
  exact pinAt_lower S v x c

/-- The two walls are retained even when one was semantically redundant
before the cut. -/
def cut (S : WeakSystem α K) (u v : α) (a b : Fin K) : WeakSystem α K :=
  lowerWall (upperWall S u a) v b

omit [Fintype α] in
@[simp] theorem valid_cut (S : WeakSystem α K) (u v : α) (a b : Fin K)
    (f : ColorMap α K) : (cut S u v a b).Valid f ↔ S.Valid f ∧ f u ≤ a ∧ b ≤ f v := by
  simp [cut, and_assoc]

theorem cut_lower (S : WeakSystem α (K + 1)) (u v x : α) (a b : Fin (K + 1)) :
    (cut S u v a b).effectiveLower x =
      if S.edge v x = true then max (S.effectiveLower x) b else S.effectiveLower x := by
  change (lowerWall (upperWall S u a) v b).effectiveLower x = _
  rw [lowerWall_lower, upperWall_lower]
  rfl

theorem cut_upper (S : WeakSystem α (K + 1)) (u v x : α) (a b : Fin (K + 1)) :
    (cut S u v a b).effectiveUpper x =
      if S.edge x u = true then min (S.effectiveUpper x) a else S.effectiveUpper x := by
  simp only [cut, lowerWall_upper, upperWall_upper]

omit [Fintype α] in
theorem cut_strict {S : WeakSystem α K} {u v : α} {a b : Fin K} (hab : a < b)
    {f : ColorMap α K} (hf : (cut S u v a b).Valid f) : f u < f v := by
  obtain ⟨_, hu, hv⟩ := (valid_cut _ _ _ _ _ _).mp hf
  exact hu.trans_lt (hab.trans_le hv)

/-- A floor cut uses the old propagated floor only as the new explicit wall
at `v`; all other primitive list endpoints remain as stored. -/
def floorCut (S : WeakSystem α (K + 1)) (u v : α) (a : Fin (K + 1)) :
    WeakSystem α (K + 1) := cut S u v a (S.effectiveLower v)

def ceilingCut (S : WeakSystem α (K + 1)) (u v : α) (b : Fin (K + 1)) :
    WeakSystem α (K + 1) := cut S u v (S.effectiveUpper u) b

@[simp] theorem valid_floorCut (S : WeakSystem α (K + 1)) (u v : α) (a : Fin (K + 1))
    (f : ColorMap α (K + 1)) : (floorCut S u v a).Valid f ↔ S.Valid f ∧ f u ≤ a := by
  rw [floorCut, valid_cut]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hf, ha⟩
    exact ⟨hf, ha, (S.valid_between_windows f hf v).1⟩

@[simp] theorem valid_ceilingCut (S : WeakSystem α (K + 1)) (u v : α) (b : Fin (K + 1))
    (f : ColorMap α (K + 1)) : (ceilingCut S u v b).Valid f ↔ S.Valid f ∧ b ≤ f v := by
  rw [ceilingCut, valid_cut]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hf, hb⟩
    exact ⟨hf, (S.valid_between_windows f hf u).2, hb⟩

theorem floorCut_lower (S : WeakSystem α (K + 1)) (hS : S.Closed) (u v x : α)
    (a : Fin (K + 1)) : (floorCut S u v a).effectiveLower x = S.effectiveLower x := by
  rw [floorCut, cut_lower]
  split_ifs with hvx
  · exact max_eq_left (S.effectiveLower_mono hS hvx)
  · rfl

theorem ceilingCut_upper (S : WeakSystem α (K + 1)) (hS : S.Closed) (u v x : α)
    (b : Fin (K + 1)) : (ceilingCut S u v b).effectiveUpper x = S.effectiveUpper x := by
  rw [ceilingCut, cut_upper]
  split_ifs with hxu
  · exact min_eq_left (S.effectiveUpper_mono hS hxu)
  · rfl

/-- A strict floor gap prevents the cut from creating a new free singleton. -/
theorem floorCut_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) (u v : α) (a : Fin (K + 1))
    (ha : S.effectiveLower u < a) : Invariant (floorCut S u v a) pins := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  have hleast := S.effectiveLower_valid h.closed hw
  have hnew : (floorCut S u v a).Valid S.effectiveLower :=
    (valid_floorCut _ _ _ _ _).mpr ⟨hleast, ha.le⟩
  refine ⟨⟨h.closed.refl, h.closed.trans⟩, h.antisymm, ⟨_, hnew⟩, ?_, ?_⟩
  · intro f hf x c hx
    exact h.pins_valid f ((valid_floorCut _ _ _ _ _).mp hf).1 x c hx
  · intro x hx
    rw [floorCut_lower S h.closed]
    change S.effectiveLower x < (cut S u v a (S.effectiveLower v)).effectiveUpper x
    rw [cut_upper]
    split_ifs with hxu
    · exact lt_min (h.free_window x hx) ((S.effectiveLower_mono h.closed hxu).trans_lt ha)
    · exact h.free_window x hx

theorem ceilingCut_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) (u v : α) (b : Fin (K + 1))
    (hb : b < S.effectiveUpper v) : Invariant (ceilingCut S u v b) pins := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  have hgreatest := S.effectiveUpper_valid h.closed hw
  have hnew : (ceilingCut S u v b).Valid S.effectiveUpper :=
    (valid_ceilingCut _ _ _ _ _).mpr ⟨hgreatest, hb.le⟩
  refine ⟨⟨h.closed.refl, h.closed.trans⟩, h.antisymm, ⟨_, hnew⟩, ?_, ?_⟩
  · intro f hf x c hx
    exact h.pins_valid f ((valid_ceilingCut _ _ _ _ _).mp hf).1 x c hx
  · intro x hx
    rw [ceilingCut_upper S h.closed]
    change (cut S u v (S.effectiveUpper u) b).effectiveLower x < S.effectiveUpper x
    rw [cut_lower]
    split_ifs with hvx
    · exact max_lt (h.free_window x hx) (hb.trans_le (S.effectiveUpper_mono h.closed hvx))
    · exact h.free_window x hx

/-- Inclusive effective width. -/
def width (S : WeakSystem α (K + 1)) (x : α) : ℕ :=
  (S.effectiveUpper x).val + 1 - (S.effectiveLower x).val

def previousColor (c : Fin (K + 1)) : Fin (K + 1) :=
  ⟨c.val - 1, (Nat.sub_le _ _).trans_lt c.isLt⟩

def nextColor (c : Fin (K + 1)) : Fin (K + 1) :=
  ⟨min (c.val + 1) K, Nat.lt_succ_of_le (min_le_right _ _)⟩

omit [DecidableEq α] in
/-- Width ratio greater than two places the floor cut strictly above the
broader endpoint's old floor and strictly below the narrower floor. -/
theorem floor_gap_of_width {S : WeakSystem α (K + 1)} (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {u v : α} (huv : S.edge u v = true)
    (hratio : 2 * width S v < width S u) :
    S.effectiveLower u < previousColor (S.effectiveLower v) ∧
      previousColor (S.effectiveLower v) < S.effectiveLower v := by
  have hwu := (S.feasible_iff_windows hS).mp hne u
  have hwv := (S.feasible_iff_windows hS).mp hne v
  have hupper := S.effectiveUpper_mono hS huv
  dsimp [width] at hratio
  change (S.effectiveLower u).val < (S.effectiveLower v).val - 1 ∧
    (S.effectiveLower v).val - 1 < (S.effectiveLower v).val
  omega

omit [DecidableEq α] in
theorem ceiling_gap_of_width {S : WeakSystem α (K + 1)} (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {u v : α} (huv : S.edge u v = true)
    (hratio : 2 * width S u < width S v) :
    S.effectiveUpper u < nextColor (S.effectiveUpper u) ∧
      nextColor (S.effectiveUpper u) < S.effectiveUpper v := by
  have hwu := (S.feasible_iff_windows hS).mp hne u
  have hwv := (S.feasible_iff_windows hS).mp hne v
  have hlower := S.effectiveLower_mono hS huv
  have hmax := (S.effectiveUpper v).isLt
  dsimp [width] at hratio
  have hnext : min ((S.effectiveUpper u).val + 1) K = (S.effectiveUpper u).val + 1 :=
    min_eq_left (by omega)
  change (S.effectiveUpper u).val < min ((S.effectiveUpper u).val + 1) K ∧
    min ((S.effectiveUpper u).val + 1) K < (S.effectiveUpper v).val
  rw [hnext]
  omega

def lowerWidthCut (S : WeakSystem α (K + 1)) (u v : α) : WeakSystem α (K + 1) :=
  floorCut S u v (previousColor (S.effectiveLower v))

def upperWidthCut (S : WeakSystem α (K + 1)) (u v : α) : WeakSystem α (K + 1) :=
  ceilingCut S u v (nextColor (S.effectiveUpper u))

theorem lowerWidthCut_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {u v : α}
    (huv : S.edge u v = true) (hratio : 2 * width S v < width S u) :
    Invariant (lowerWidthCut S u v) pins :=
  floorCut_invariant h u v _ (floor_gap_of_width h.closed h.feasible huv hratio).1

theorem upperWidthCut_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {u v : α}
    (huv : S.edge u v = true) (hratio : 2 * width S u < width S v) :
    Invariant (upperWidthCut S u v) pins :=
  ceilingCut_invariant h u v _ (ceiling_gap_of_width h.closed h.feasible huv hratio).2

omit [Fintype α] in
theorem cut_lower_tightens (S : WeakSystem α K) (u v x : α) (a b : Fin K) :
    S.lower x ≤ (cut S u v a b).lower x := by
  simp only [cut, lowerWall, upperWall]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [Fintype α] in
theorem cut_upper_tightens (S : WeakSystem α K) (u v x : α) (a b : Fin K) :
    (cut S u v a b).upper x ≤ S.upper x := by
  simp only [cut, lowerWall, upperWall]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

omit [Fintype α] [DecidableEq α] in
theorem pinBounds_of_tightening {S T : WeakSystem α K}
    {pins : α → Option (Fin K)} (hp : PinBounds S pins)
    (hlo : ∀ x, S.lower x ≤ T.lower x) (hhi : ∀ x, T.upper x ≤ S.upper x)
    (hne : ∃ f, T.Valid f) : PinBounds T pins := by
  obtain ⟨f, hf⟩ := hne
  intro x c hx
  obtain ⟨hl, hu⟩ := hp x c hx
  have hlow : c ≤ T.lower x := hl ▸ hlo x
  have hupp : T.upper x ≤ c := hu ▸ hhi x
  exact ⟨le_antisymm ((hf.1 x).1.trans ((hf.1 x).2.trans hupp)) hlow,
    le_antisymm hupp (hlow.trans ((hf.1 x).1.trans (hf.1 x).2))⟩

omit [Fintype α] in
theorem cut_pinBounds {S : WeakSystem α K} {pins : α → Option (Fin K)}
    (hp : PinBounds S pins) (u v : α) (a b : Fin K)
    (hne : ∃ f, (cut S u v a b).Valid f) : PinBounds (cut S u v a b) pins :=
  pinBounds_of_tightening hp (fun x => cut_lower_tightens S u v x a b)
    (fun x => cut_upper_tightens S u v x a b) hne

theorem lowerWidthCut_pinBounds {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) (hp : PinBounds S pins)
    {u v : α} (huv : S.edge u v = true) (hratio : 2 * width S v < width S u) :
    PinBounds (lowerWidthCut S u v) pins :=
  cut_pinBounds hp _ _ _ _ (lowerWidthCut_invariant h huv hratio).feasible

theorem upperWidthCut_pinBounds {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) (hp : PinBounds S pins)
    {u v : α} (huv : S.edge u v = true) (hratio : 2 * width S u < width S v) :
    PinBounds (upperWidthCut S u v) pins :=
  cut_pinBounds hp _ _ _ _ (upperWidthCut_invariant h huv hratio).feasible

/-- Retire one generating numerical row. This is not the public relation. -/
def retireRow (S : WeakSystem α K) (u v : α) : WeakSystem α K where
  edge x y := if x = u ∧ y = v then false else S.edge x y
  lower := S.lower
  upper := S.upper

omit [Fintype α] in
@[simp] theorem retireRow_removed (S : WeakSystem α K) (u v : α) :
    (retireRow S u v).edge u v = false := by simp [retireRow]

omit [Fintype α] in
theorem retireRow_valid (S : WeakSystem α K) (u v : α) (hwall : S.upper u ≤ S.lower v)
    (f : ColorMap α K) : (retireRow S u v).Valid f ↔ S.Valid f := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro x y hxy
    by_cases h : x = u ∧ y = v
    · obtain ⟨hxu, hyv⟩ := h
      subst x
      subst y
      exact (hf.1 u).2.trans (hwall.trans (hf.1 v).1)
    · exact hf.2 x y (by simpa only [retireRow, if_neg h] using hxy)
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro x y hxy
    have h : ¬(x = u ∧ y = v) := by
      intro hh
      simp only [retireRow, if_pos hh, Bool.false_eq_true] at hxy
    exact hf.2 x y (by simpa only [retireRow, if_neg h] using hxy)

theorem retireRow_maps (S : WeakSystem α K) (u v : α) (hwall : S.upper u ≤ S.lower v) :
    (retireRow S u v).maps = S.maps := by
  ext f
  simp only [mem_maps, retireRow_valid S u v hwall]

theorem retireRow_count (S : WeakSystem α K) (u v : α) (hwall : S.upper u ≤ S.lower v) :
    (retireRow S u v).count = S.count := by
  simp only [count, retireRow_maps S u v hwall]

omit [Fintype α] in
theorem cut_walls_strict (S : WeakSystem α K) (u v : α) (a b : Fin K) (hab : a < b) :
    (cut S u v a b).upper u < (cut S u v a b).lower v := by
  change (if u = u then min (S.upper u) a else S.upper u) <
    (if v = v then max (S.lower v) b else S.lower v)
  simp only [ite_true]
  exact (min_le_right _ _).trans_lt (hab.trans_le (le_max_right _ _))

omit [Fintype α] in
theorem retire_cut_valid (S : WeakSystem α K) (u v : α) (a b : Fin K) (hab : a < b)
    (f : ColorMap α K) :
    (retireRow (cut S u v a b) u v).Valid f ↔ (cut S u v a b).Valid f :=
  retireRow_valid _ _ _ (cut_walls_strict S u v a b hab).le f

theorem retire_cut_count (S : WeakSystem α K) (u v : α) (a b : Fin K) (hab : a < b) :
    (retireRow (cut S u v a b) u v).count = (cut S u v a b).count :=
  retireRow_count _ _ _ (cut_walls_strict S u v a b hab).le

theorem lowerWidthCut_strict {S : WeakSystem α (K + 1)} (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {u v : α} (huv : S.edge u v = true)
    (hratio : 2 * width S v < width S u) {f : ColorMap α (K + 1)}
    (hf : (lowerWidthCut S u v).Valid f) : f u < f v :=
  cut_strict (floor_gap_of_width hS hne huv hratio).2 hf

theorem upperWidthCut_strict {S : WeakSystem α (K + 1)} (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {u v : α} (huv : S.edge u v = true)
    (hratio : 2 * width S u < width S v) {f : ColorMap α (K + 1)}
    (hf : (upperWidthCut S u v).Valid f) : f u < f v :=
  cut_strict (ceiling_gap_of_width hS hne huv hratio).1 hf

/-- The maps discarded by the lower-width cut. -/
def lowerDiscarded (S : WeakSystem α (K + 1)) (u v : α) : Finset (ColorMap α (K + 1)) :=
  S.maps.filter (fun f => previousColor (S.effectiveLower v) < f u)

/-- The maps discarded by the upper-width cut. -/
def upperDiscarded (S : WeakSystem α (K + 1)) (u v : α) : Finset (ColorMap α (K + 1)) :=
  S.maps.filter (fun f => f v < nextColor (S.effectiveUpper u))

theorem lowerWidthCut_maps (S : WeakSystem α (K + 1)) (u v : α) :
    (lowerWidthCut S u v).maps =
      S.maps.filter (fun f => f u ≤ previousColor (S.effectiveLower v)) := by
  ext f
  simp [lowerWidthCut]

theorem upperWidthCut_maps (S : WeakSystem α (K + 1)) (u v : α) :
    (upperWidthCut S u v).maps =
      S.maps.filter (fun f => nextColor (S.effectiveUpper u) ≤ f v) := by
  ext f
  simp [upperWidthCut]

theorem lower_count_partition (S : WeakSystem α (K + 1)) (u v : α) :
    (lowerWidthCut S u v).count + (lowerDiscarded S u v).card = S.count := by
  simp only [count, lowerWidthCut_maps, lowerDiscarded]
  simpa only [not_le] using Finset.card_filter_add_card_filter_not (s := S.maps)
    (fun f => f u ≤ previousColor (S.effectiveLower v))

theorem upper_count_partition (S : WeakSystem α (K + 1)) (u v : α) :
    (upperWidthCut S u v).count + (upperDiscarded S u v).card = S.count := by
  simp only [count, upperWidthCut_maps, upperDiscarded]
  simpa only [not_le] using Finset.card_filter_add_card_filter_not (s := S.maps)
    (fun f => nextColor (S.effectiveUpper u) ≤ f v)

/-- The exact integer support interval used in the insertion estimate. -/
def windowColors (S : WeakSystem α (K + 1)) (v : α) : Finset ℤ :=
  Finset.Icc ((S.effectiveLower v).val : ℤ) (S.effectiveUpper v).val

omit [DecidableEq α] in
theorem card_windowColors (S : WeakSystem α (K + 1)) (v : α) :
    (windowColors S v).card = width S v := by
  rw [windowColors, Int.card_Icc]
  unfold width
  omega

theorem lowerDiscarded_subset {n : ℕ} (S : WeakSystem (Fin n) (K + 1))
    {u v : Fin n} (huv : S.edge u v = true) :
    lowerDiscarded S u v ⊆ FiniteInsertion.restrictedMaps S u (windowColors S v) := by
  intro f hf
  obtain ⟨hf, hbad⟩ := Finset.mem_filter.mp hf
  have hvalid := (mem_maps S f).mp hf
  have hrow := hvalid.2 u v huv
  have hupper := (S.valid_between_windows f hvalid v).2
  refine Finset.mem_filter.mpr ⟨hf, ?_⟩
  change ((f u).val : ℤ) ∈ Finset.Icc _ _
  rw [Finset.mem_Icc]
  change (S.effectiveLower v).val - 1 < (f u).val at hbad
  constructor <;> omega

theorem upperDiscarded_subset {n : ℕ} (S : WeakSystem (Fin n) (K + 1))
    {u v : Fin n} (huv : S.edge u v = true) :
    upperDiscarded S u v ⊆ FiniteInsertion.restrictedMaps S v (windowColors S u) := by
  intro f hf
  obtain ⟨hf, hbad⟩ := Finset.mem_filter.mp hf
  have hvalid := (mem_maps S f).mp hf
  have hrow := hvalid.2 u v huv
  have hlower := (S.valid_between_windows f hvalid u).1
  refine Finset.mem_filter.mpr ⟨hf, ?_⟩
  change ((f v).val : ℤ) ∈ Finset.Icc _ _
  rw [Finset.mem_Icc]
  change (f v).val < min ((S.effectiveUpper u).val + 1) K at hbad
  have hnext := min_le_left ((S.effectiveUpper u).val + 1) K
  constructor <;> omega

/-- Lost maps times the broad width are bounded by the insertion constant
times the narrow width times the original map count. -/
theorem lower_loss_mul_width {n : ℕ} (C : FiniteInsertion.OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) {u v : Fin n} (huv : C.system.edge u v = true) :
    (lowerDiscarded C.system u v).card * width C.system u ≤
      2 * 4 ^ FiniteInsertion.comparableCount C u * width C.system v * C.system.count := by
  have h := FiniteInsertion.restricted_count_bound C hne u (windowColors C.system v)
  rw [card_windowColors] at h
  exact (Nat.mul_le_mul_right _ (Finset.card_le_card (lowerDiscarded_subset C.system huv))).trans h

theorem upper_loss_mul_width {n : ℕ} (C : FiniteInsertion.OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) {u v : Fin n} (huv : C.system.edge u v = true) :
    (upperDiscarded C.system u v).card * width C.system v ≤
      2 * 4 ^ FiniteInsertion.comparableCount C v * width C.system u * C.system.count := by
  have h := FiniteInsertion.restricted_count_bound C hne v (windowColors C.system u)
  rw [card_windowColors] at h
  exact (Nat.mul_le_mul_right _ (Finset.card_le_card (upperDiscarded_subset C.system huv))).trans h

/-- Elementary normalization of an exact count-loss inequality. -/
theorem retention_of_loss_bound {good bad total broad narrow constant : ℕ}
    (hpart : good + bad = total) (htotal : 0 < total) (hnarrow : 0 < narrow)
    (hloss : bad * broad ≤ constant * narrow * total)
    (L : ℚ) (hL : 0 < L) (hscale : L * narrow ≤ broad) :
    1 - (constant : ℚ) / L ≤ (good : ℚ) / total := by
  have htotal' : (0 : ℚ) < total := by exact_mod_cast htotal
  have hnarrow' : (0 : ℚ) < narrow := by exact_mod_cast hnarrow
  have hloss' : (bad : ℚ) * broad ≤ constant * narrow * total := by exact_mod_cast hloss
  have hpart' : (good : ℚ) + bad = total := by exact_mod_cast hpart
  have hscaled : (bad : ℚ) * L ≤ constant * total := by
    have hprod : ((bad : ℚ) * L) * narrow ≤ ((constant : ℚ) * total) * narrow := by
      calc
        (bad : ℚ) * L * narrow = bad * (L * narrow) := by ring
        _ ≤ bad * broad := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
        _ ≤ constant * narrow * total := hloss'
        _ = constant * total * narrow := by ring
    exact le_of_mul_le_mul_right hprod hnarrow'
  have hfrac : (bad : ℚ) / total ≤ (constant : ℚ) / L :=
    (div_le_div_iff₀ htotal' hL).mpr hscaled
  have hsum : (good : ℚ) / total + (bad : ℚ) / total = 1 := by
    rw [← add_div, hpart', div_self htotal'.ne']
  linarith

/-- A lower-width normalization retains at least `1-C/L` of the true maps,
with the explicit insertion constant `C = 2 * 4^comparableCount`. -/
theorem lower_retention {n : ℕ} (C : FiniteInsertion.OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) {u v : Fin n} (huv : C.system.edge u v = true)
    (L : ℚ) (hL : 0 < L)
    (hscale : L * (width C.system v : ℚ) ≤ width C.system u) :
    1 - (2 * 4 ^ FiniteInsertion.comparableCount C u : ℚ) / L ≤
      ((lowerWidthCut C.system u v).count : ℚ) / C.system.count := by
  have h := retention_of_loss_bound (lower_count_partition C.system u v)
    (C.system.count_pos_iff.mpr hne) (FiniteInsertion.windowWidth_pos C hne v)
    (lower_loss_mul_width C hne huv) L hL hscale
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using h

theorem upper_retention {n : ℕ} (C : FiniteInsertion.OrderedSystem n K)
    (hne : ∃ f, C.system.Valid f) {u v : Fin n} (huv : C.system.edge u v = true)
    (L : ℚ) (hL : 0 < L)
    (hscale : L * (width C.system u : ℚ) ≤ width C.system v) :
    1 - (2 * 4 ^ FiniteInsertion.comparableCount C v : ℚ) / L ≤
      ((upperWidthCut C.system u v).count : ℚ) / C.system.count := by
  have h := retention_of_loss_bound (upper_count_partition C.system u v)
    (C.system.count_pos_iff.mpr hne) (FiniteInsertion.windowWidth_pos C hne u)
    (upper_loss_mul_width C hne huv) L hL hscale
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using h

omit [Fintype α] in
/-- Identical explicit walls can be installed in any two representations of
the same finite law, for example the public closure and sparse numerical rows. -/
theorem cut_valid_congr (S T : WeakSystem α K)
    (heq : ∀ f, T.Valid f ↔ S.Valid f) (u v : α) (a b : Fin K) (f : ColorMap α K) :
    (cut T u v a b).Valid f ↔ (cut S u v a b).Valid f := by
  simp only [valid_cut, heq]

theorem cut_count_congr (S T : WeakSystem α K)
    (heq : ∀ f, T.Valid f ↔ S.Valid f) (u v : α) (a b : Fin K) :
    (cut T u v a b).count = (cut S u v a b).count := by
  have hm : (cut T u v a b).maps = (cut S u v a b).maps := by
    ext f
    simp only [mem_maps, cut_valid_congr S T heq]
  exact congrArg Finset.card hm

theorem lowerWidthCut_retire_count {S : WeakSystem α (K + 1)} (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {u v : α} (huv : S.edge u v = true)
    (hratio : 2 * width S v < width S u) :
    (retireRow (lowerWidthCut S u v) u v).count = (lowerWidthCut S u v).count :=
  retire_cut_count _ _ _ _ _ (floor_gap_of_width hS hne huv hratio).2

theorem upperWidthCut_retire_count {S : WeakSystem α (K + 1)} (hS : S.Closed)
    (hne : ∃ f, S.Valid f) {u v : α} (huv : S.edge u v = true)
    (hratio : 2 * width S u < width S v) :
    (retireRow (upperWidthCut S u v) u v).count = (upperWidthCut S u v).count :=
  retire_cut_count _ _ _ _ _ (ceiling_gap_of_width hS hne huv hratio).1

end SortingAdversary.Optimal.CutNormalization
