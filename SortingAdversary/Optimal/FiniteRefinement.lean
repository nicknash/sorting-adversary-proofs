import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.Refinement

/-!
# A colour split on actual finite weak-map systems

This file assembles both endpoint refinements into a `WeakSystem`, including
finite palette bounds, unchanged physical pin identities, and the final new
pin.  The count inequalities follow from explicit injections of the selected
old fibre; feasibility of the refined assignments is proved, not assumed.

`pins` identifies coordinates already fixed physically.  Their old lower and
upper bounds must both equal that pin.  At all other coordinates the stored
bounds are artificial lists, lifted by inverse image under colour collapse.
Raw rows are retained.  The supplied rows are assumed reflexively transitively
closed for the equal-colour-successor operation; sparse raw rows require a
separate public-closure representation with equivalent map semantics.
-/

namespace SortingAdversary.Optimal.FiniteRefinement

open WeakMaps

variable {α : Type*} {K : ℕ}

/-- The greatest new colour collapsing to an old colour at most `u`. -/
def upperEnd (c u : ℕ) : ℕ := if u < c then u else u + 1

theorem lower_bound_iff (c l x : ℕ) :
    Refinement.embed c l ≤ x ↔ l ≤ Refinement.collapse c x := by
  unfold Refinement.embed Refinement.collapse
  split_ifs <;> omega

theorem upper_bound_iff (c u x : ℕ) :
    x ≤ upperEnd c u ↔ Refinement.collapse c x ≤ u := by
  unfold upperEnd Refinement.collapse
  split_ifs <;> omega

/-- The chronological inclusion of an old finite colour identity. -/
def embedColor (c d : Fin K) : Fin (K + 1) :=
  ⟨Refinement.embed c.val d.val, by
    have hd := d.isLt
    unfold Refinement.embed
    split_ifs <;> omega⟩

/-- The upper endpoint of the inverse image of an inclusive artificial list. -/
def upperColor (c d : Fin K) : Fin (K + 1) :=
  ⟨upperEnd c.val d.val, by
    have hd := d.isLt
    unfold upperEnd
    split_ifs <;> omega⟩

/-- The fresh colour immediately above the old colour `c`. -/
def freshColor (c : Fin K) : Fin (K + 1) := ⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩

@[simp] theorem embedColor_val (c d : Fin K) :
    (embedColor c d).val = Refinement.embed c.val d.val := rfl

@[simp] theorem upperColor_val (c d : Fin K) :
    (upperColor c d).val = upperEnd c.val d.val := rfl

@[simp] theorem freshColor_val (c : Fin K) : (freshColor c).val = c.val + 1 := rfl

/-- Intersect one coordinate's current list with a singleton.  Taking a pin
outside its list makes the system infeasible; it never enlarges the list. -/
def pinAt [DecidableEq α] (S : WeakSystem α K) (v : α) (d : Fin K) : WeakSystem α K where
  edge := S.edge
  lower x := if x = v then max (S.lower x) d else S.lower x
  upper x := if x = v then min (S.upper x) d else S.upper x

@[simp] theorem valid_pinAt [DecidableEq α] (S : WeakSystem α K) (v : α) (d : Fin K)
    (f : ColorMap α K) : (pinAt S v d).Valid f ↔ S.Valid f ∧ f v = d := by
  constructor
  · intro hf
    have hv : max (S.lower v) d ≤ f v ∧ f v ≤ min (S.upper v) d := by
      simpa only [pinAt, if_pos rfl, ite_true] using hf.1 v
    have heq : f v = d :=
      le_antisymm (le_trans hv.2 (min_le_right _ _))
        (le_trans (le_max_right _ _) hv.1)
    refine ⟨⟨?_, hf.2⟩, heq⟩
    intro x
    by_cases hx : x = v
    · subst x
      exact ⟨le_trans (le_max_left _ _) hv.1, le_trans hv.2 (min_le_left _ _)⟩
    · simpa only [pinAt, if_neg hx] using hf.1 x
  · rintro ⟨hf, heq⟩
    refine ⟨?_, hf.2⟩
    intro x
    by_cases hx : x = v
    · subst x
      have hv := hf.1 v
      simpa only [pinAt, if_pos rfl, ite_true, heq, max_le_iff, le_min_iff, le_refl,
        and_true, true_and] using hv
    · simpa only [pinAt, if_neg hx] using hf.1 x

/-- Split artificial lists by collapse, but preserve the singleton identity of
each physical pin.  In particular a physical pin at `c` does not acquire `c+`. -/
def splitPalette (S : WeakSystem α K) (pins : α → Option (Fin K)) (c : Fin K) :
    WeakSystem α (K + 1) where
  edge := S.edge
  lower x := match pins x with
    | some d => embedColor c d
    | none => embedColor c (S.lower x)
  upper x := match pins x with
    | some d => embedColor c d
    | none => upperColor c (S.upper x)

/-- The actual lower-endpoint repair: refine the alphabet, then pin the
selected coordinate to the fresh colour. -/
def lowerRefinement [DecidableEq α] (S : WeakSystem α K) (pins : α → Option (Fin K))
    (v : α) (c : Fin K) : WeakSystem α (K + 1) :=
  pinAt (splitPalette S pins c) v (freshColor c)

/-- Physical pins are represented by singleton bounds in the old system. -/
def PinBounds (S : WeakSystem α K) (pins : α → Option (Fin K)) : Prop :=
  ∀ x d, pins x = some d → S.lower x = d ∧ S.upper x = d

/-- Every feasible map obeys the old physical pin identities. -/
theorem valid_pin_value (S : WeakSystem α K) (pins : α → Option (Fin K))
    (hpins : PinBounds S pins) {f : ColorMap α K} (hf : S.Valid f)
    {x : α} {d : Fin K} (hx : pins x = some d) : f x = d := by
  obtain ⟨hl, hu⟩ := hpins x d hx
  exact le_antisymm (hu ▸ (hf.1 x).2) (hl ▸ (hf.1 x).1)

/-- The finite version of raising the selected equal-colour upper set. -/
def liftAssignment (S : WeakSystem α K) (v : α) (c : Fin K) (f : ColorMap α K) :
    ColorMap α (K + 1) :=
  fun x => ⟨Refinement.liftMap (fun a b => S.edge a b = true)
    v c.val (fun a => (f a).val) x,
    Refinement.liftMap_palette (fun a b => S.edge a b = true)
      (fun a => (f a).isLt) x⟩

@[simp] theorem collapse_liftAssignment (S : WeakSystem α K) (v : α) (c : Fin K)
    (f : ColorMap α K) (x : α) :
    Refinement.collapse c.val (liftAssignment S v c f x).val = (f x).val := by
  exact Refinement.collapse_liftMap (fun a b => S.edge a b = true) v c.val
    (fun a => (f a).val) x

theorem liftAssignment_injective (S : WeakSystem α K) (v : α) (c : Fin K) :
    Function.Injective (liftAssignment S v c) := by
  intro f g h
  funext x
  apply Fin.ext
  have hx := congrArg (fun k : ColorMap α (K + 1) =>
    Refinement.collapse c.val (k x).val) h
  simpa only [collapse_liftAssignment] using hx

def liftEmbedding (S : WeakSystem α K) (v : α) (c : Fin K) :
    ColorMap α K ↪ ColorMap α (K + 1) :=
  ⟨liftAssignment S v c, liftAssignment_injective S v c⟩

/-- A higher attainable value excludes old pins at `c` from the selected
vertex's upper set.  This fact is derived from old feasibility. -/
theorem excludes_pinned_successor (S : WeakSystem α K)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    {v : α} {c : Fin K} {g : ColorMap α K} (hg : S.Valid g) (hhi : c < g v)
    {x : α} {d : Fin K} (hx : pins x = some d) :
    ¬ (d.val = c.val ∧ S.edge v x = true) := by
  rintro ⟨hd, hvx⟩
  have hval := valid_pin_value S pins hpins hg hx
  have hle := hg.2 v x hvx
  have hdc : d = c := Fin.ext hd
  rw [hval, hdc] at hle
  exact (not_le_of_gt hhi) hle

/-- The lifted map satisfies every artificial list, every immutable physical
pin, and every raw row in the actual split system. -/
theorem liftAssignment_valid_split (S : WeakSystem α K) (hS : S.Closed)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    {v : α} {c : Fin K} {g f : ColorMap α K}
    (hg : S.Valid g) (hhi : c < g v) (hf : S.Valid f) :
    (splitPalette S pins c).Valid (liftAssignment S v c f) := by
  constructor
  · intro x
    cases hx : pins x with
    | none =>
        simp only [splitPalette, hx]
        constructor
        · apply (lower_bound_iff c.val (S.lower x).val _).mpr
          simpa only [collapse_liftAssignment, Fin.le_def] using (hf.1 x).1
        · apply (upper_bound_iff c.val (S.upper x).val _).mpr
          simpa only [collapse_liftAssignment, Fin.le_def] using (hf.1 x).2
    | some d =>
        have hval := valid_pin_value S pins hpins hf hx
        have hnot := excludes_pinned_successor S pins hpins hg hhi hx
        have heq : liftAssignment S v c f x = embedColor c d := by
          apply Fin.ext
          exact Refinement.liftMap_pin (fun a b => S.edge a b = true)
            (v := v) (p := x) (c := c.val) (d := d.val) (f := fun a => (f a).val)
            (congrArg Fin.val hval) hnot
        simp only [splitPalette, hx]
        change embedColor c d ≤ liftAssignment S v c f x ∧
          liftAssignment S v c f x ≤ embedColor c d
        exact ⟨heq.ge, heq.le⟩
  · intro x y hxy
    exact Refinement.liftMap_respects (fun a b => S.edge a b = true)
      (fun {_ _ _} hab hbc => hS.trans _ _ _ hab hbc)
      (fun a b hab => hf.2 a b hab) x y hxy

/-- Every map of the selected old fibre becomes a map of the actual refined
and pinned system. -/
theorem liftAssignment_valid_refinement [DecidableEq α] (S : WeakSystem α K) (hS : S.Closed)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    {v : α} {c : Fin K} {g f : ColorMap α K}
    (hg : S.Valid g) (hhi : c < g v) (hf : S.Valid f) (hfc : f v = c) :
    (lowerRefinement S pins v c).Valid (liftAssignment S v c f) := by
  apply (valid_pinAt _ _ _ _).mpr
  refine ⟨liftAssignment_valid_split S hS pins hpins hg hhi hf, ?_⟩
  apply Fin.ext
  exact Refinement.liftMap_selected (fun a b => S.edge a b = true)
    (v := v) (c := c.val) (f := fun a => (f a).val)
    (hS.refl v) (congrArg Fin.val hfc)

/-! ## The upper endpoint

The fresh colour now has index `c`, and the old identity at `c` becomes `c+1`.
Both endpoint splits use the same collapse map and therefore the same lifted
artificial interval bounds.  Only the immutable pin embedding and the chosen
equal-colour upper/lower set change.
-/

def embedColorBefore (c d : Fin K) : Fin (K + 1) :=
  ⟨Refinement.embedBefore c.val d.val, by
    have hd := d.isLt
    unfold Refinement.embedBefore
    split_ifs <;> omega⟩

@[simp] theorem embedColorBefore_val (c d : Fin K) :
    (embedColorBefore c d).val = Refinement.embedBefore c.val d.val := rfl

/-- Split below `c`: all old physical pins keep their identities, while all
artificial intervals are inverse images under the same collapse map. -/
def splitPaletteBefore (S : WeakSystem α K) (pins : α → Option (Fin K)) (c : Fin K) :
    WeakSystem α (K + 1) where
  edge := S.edge
  lower x := match pins x with
    | some d => embedColorBefore c d
    | none => embedColor c (S.lower x)
  upper x := match pins x with
    | some d => embedColorBefore c d
    | none => upperColor c (S.upper x)

def upperRefinement [DecidableEq α] (S : WeakSystem α K)
    (pins : α → Option (Fin K)) (v : α) (c : Fin K) : WeakSystem α (K + 1) :=
  pinAt (splitPaletteBefore S pins c) v c.castSucc

def liftAssignmentBefore (S : WeakSystem α K) (v : α) (c : Fin K)
    (f : ColorMap α K) : ColorMap α (K + 1) :=
  fun x => ⟨Refinement.liftMapBefore (fun a b => S.edge a b = true)
    v c.val (fun a => (f a).val) x,
    Refinement.liftMapBefore_palette (fun a b => S.edge a b = true)
      (fun a => (f a).isLt) x⟩

@[simp] theorem collapse_liftAssignmentBefore (S : WeakSystem α K) (v : α) (c : Fin K)
    (f : ColorMap α K) (x : α) :
    Refinement.collapse c.val (liftAssignmentBefore S v c f x).val = (f x).val := by
  exact Refinement.collapse_liftMapBefore (fun a b => S.edge a b = true) v c.val
    (fun a => (f a).val) x

theorem liftAssignmentBefore_injective (S : WeakSystem α K) (v : α) (c : Fin K) :
    Function.Injective (liftAssignmentBefore S v c) := by
  intro f g h
  funext x
  apply Fin.ext
  have hx := congrArg (fun k : ColorMap α (K + 1) =>
    Refinement.collapse c.val (k x).val) h
  simpa only [collapse_liftAssignmentBefore] using hx

def liftEmbeddingBefore (S : WeakSystem α K) (v : α) (c : Fin K) :
    ColorMap α K ↪ ColorMap α (K + 1) :=
  ⟨liftAssignmentBefore S v c, liftAssignmentBefore_injective S v c⟩

/-- A lower attainable value excludes old pins at `c` from the selected
vertex's lower set. -/
theorem excludes_pinned_predecessor (S : WeakSystem α K)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    {v : α} {c : Fin K} {g : ColorMap α K} (hg : S.Valid g) (hlo : g v < c)
    {x : α} {d : Fin K} (hx : pins x = some d) :
    ¬ (d.val = c.val ∧ S.edge x v = true) := by
  rintro ⟨hd, hxv⟩
  have hval := valid_pin_value S pins hpins hg hx
  have hle := hg.2 x v hxv
  have hdc : d = c := Fin.ext hd
  rw [hval, hdc] at hle
  exact (not_le_of_gt hlo) hle

theorem liftAssignmentBefore_valid_split (S : WeakSystem α K) (hS : S.Closed)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    {v : α} {c : Fin K} {g f : ColorMap α K}
    (hg : S.Valid g) (hlo : g v < c) (hf : S.Valid f) :
    (splitPaletteBefore S pins c).Valid (liftAssignmentBefore S v c f) := by
  constructor
  · intro x
    cases hx : pins x with
    | none =>
        simp only [splitPaletteBefore, hx]
        constructor
        · apply (lower_bound_iff c.val (S.lower x).val _).mpr
          simpa only [collapse_liftAssignmentBefore, Fin.le_def] using (hf.1 x).1
        · apply (upper_bound_iff c.val (S.upper x).val _).mpr
          simpa only [collapse_liftAssignmentBefore, Fin.le_def] using (hf.1 x).2
    | some d =>
        have hval := valid_pin_value S pins hpins hf hx
        have hnot := excludes_pinned_predecessor S pins hpins hg hlo hx
        have heq : liftAssignmentBefore S v c f x = embedColorBefore c d := by
          apply Fin.ext
          exact Refinement.liftMapBefore_pin (fun a b => S.edge a b = true)
            (v := v) (p := x) (c := c.val) (d := d.val) (f := fun a => (f a).val)
            (congrArg Fin.val hval) hnot
        simp only [splitPaletteBefore, hx]
        change embedColorBefore c d ≤ liftAssignmentBefore S v c f x ∧
          liftAssignmentBefore S v c f x ≤ embedColorBefore c d
        exact ⟨heq.ge, heq.le⟩
  · intro x y hxy
    exact Refinement.liftMapBefore_respects (fun a b => S.edge a b = true)
      (fun {_ _ _} hab hbc => hS.trans _ _ _ hab hbc)
      (fun a b hab => hf.2 a b hab) x y hxy

/-- The upper-endpoint lift belongs to the actual split-and-pinned system. -/
theorem liftAssignmentBefore_valid_refinement [DecidableEq α]
    (S : WeakSystem α K) (hS : S.Closed)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    {v : α} {c : Fin K} {g f : ColorMap α K}
    (hg : S.Valid g) (hlo : g v < c) (hf : S.Valid f) (hfc : f v = c) :
    (upperRefinement S pins v c).Valid (liftAssignmentBefore S v c f) := by
  apply (valid_pinAt _ _ _ _).mpr
  refine ⟨liftAssignmentBefore_valid_split S hS pins hpins hg hlo hf, ?_⟩
  apply Fin.ext
  exact Refinement.liftMapBefore_selected (fun a b => S.edge a b = true)
    (v := v) (c := c.val) (f := fun a => (f a).val)
    (hS.refl v) (congrArg Fin.val hfc)

section Counts

variable [Fintype α] [DecidableEq α]

/-- Pinning without a colour split keeps exactly the selected old fibre. -/
theorem maps_pinAt (S : WeakSystem α K) (v : α) (c : Fin K) :
    (pinAt S v c).maps = S.fiber v c := by
  ext f
  simp only [WeakSystem.mem_maps, valid_pinAt, WeakSystem.mem_fiber]

/-- The lower-endpoint colour split and pin retains at least the count of the
selected old fibre.  No refined-system feasibility assumption is used. -/
theorem lower_refinement_count (S : WeakSystem α K) (hS : S.Closed)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    (v : α) (c : Fin K) (g : ColorMap α K) (hg : S.Valid g) (hhi : c < g v) :
    (S.fiber v c).card ≤ (lowerRefinement S pins v c).count := by
  have hsub : (S.fiber v c).map (liftEmbedding S v c) ⊆
      (lowerRefinement S pins v c).maps := by
    intro f hf
    obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_map.mp hf
    obtain ⟨hvalid, hfiber⟩ := (WeakSystem.mem_fiber S v c g₀).mp hg₀
    exact (WeakSystem.mem_maps _ _).mpr
      (liftAssignment_valid_refinement S hS pins hpins hg hhi hvalid hfiber)
  simpa only [Finset.card_map, WeakSystem.count] using Finset.card_le_card hsub

/-- The upper-endpoint split also retains at least the selected old fibre
count, with the lower-support witness replacing the upper-support witness. -/
theorem upper_refinement_count (S : WeakSystem α K) (hS : S.Closed)
    (pins : α → Option (Fin K)) (hpins : PinBounds S pins)
    (v : α) (c : Fin K) (g : ColorMap α K) (hg : S.Valid g) (hlo : g v < c) :
    (S.fiber v c).card ≤ (upperRefinement S pins v c).count := by
  have hsub : (S.fiber v c).map (liftEmbeddingBefore S v c) ⊆
      (upperRefinement S pins v c).maps := by
    intro f hf
    obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_map.mp hf
    obtain ⟨hvalid, hfiber⟩ := (WeakSystem.mem_fiber S v c g₀).mp hg₀
    exact (WeakSystem.mem_maps _ _).mpr
      (liftAssignmentBefore_valid_refinement S hS pins hpins hg hlo hvalid hfiber)
  simpa only [Finset.card_map, WeakSystem.count] using Finset.card_le_card hsub

end Counts
end SortingAdversary.Optimal.FiniteRefinement
