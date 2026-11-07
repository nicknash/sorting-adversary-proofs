import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Finite weak colour maps

The November 7 construction counts maps to an ordered colour palette, rather
than strict rankings.  A recorded comparison imposes a *weak* inequality on
these maps.  In particular, the two answers overlap on maps with tied colours.

This file gives the exact finite semantics of these counts, an executable
exhaustive counting rule, and the elementary guarantees that are also required
of the manuscript's local approximation engine.  Exhaustive counting is not
claimed to take polynomial time.  The local approximation engine and the
recursive controller are separate proof obligations.
-/

namespace SortingAdversary.Optimal.WeakMaps

/-- A colour assignment to finitely many labels. -/
abbrev ColorMap (α : Type*) (K : ℕ) := α → Fin K

/-- Raw comparison rows and inclusive individual colour lists.

Using a Boolean row relation makes the finite count executable.  The raw rows
need not be transitively closed: respecting them also respects their closure.
The bounds are allowed to be inconsistent, in which case there are no maps.
-/
structure WeakSystem (α : Type*) (K : ℕ) where
  edge : α → α → Bool
  lower : α → Fin K
  upper : α → Fin K

namespace WeakSystem

variable {α : Type*} {K : ℕ}

/-- A map obeys all inclusive lists and every weak comparison row. -/
def Valid (S : WeakSystem α K) (f : ColorMap α K) : Prop :=
  (∀ v, S.lower v ≤ f v ∧ f v ≤ S.upper v) ∧
    ∀ u v, S.edge u v = true → f u ≤ f v

section Finite

variable [Fintype α] [DecidableEq α]

instance instDecidableValid (S : WeakSystem α K) (f : ColorMap α K) :
    Decidable (S.Valid f) := by
  unfold Valid
  infer_instance

/-- All feasible weak maps, explicitly enumerated. -/
def maps (S : WeakSystem α K) : Finset (ColorMap α K) :=
  Finset.univ.filter S.Valid

/-- The exact, unnormalised count of weak maps. -/
def count (S : WeakSystem α K) : ℕ := S.maps.card

@[simp] theorem mem_maps (S : WeakSystem α K) (f : ColorMap α K) :
    f ∈ S.maps ↔ S.Valid f := by
  simp [maps]

theorem count_pos_iff (S : WeakSystem α K) :
    0 < S.count ↔ ∃ f, S.Valid f := by
  simp [count, Finset.card_pos, Finset.nonempty_def]

/-- Add a single raw weak comparison.  Other rows and all lists are unchanged. -/
def addRow (S : WeakSystem α K) (a b : α) : WeakSystem α K :=
  { S with edge := fun u v => S.edge u v || decide (u = a ∧ v = b) }

omit [Fintype α] in
@[simp] theorem valid_addRow (S : WeakSystem α K) (a b : α) (f : ColorMap α K) :
    (S.addRow a b).Valid f ↔ S.Valid f ∧ f a ≤ f b := by
  constructor
  · rintro ⟨hlist, hrows⟩
    refine ⟨⟨hlist, ?_⟩, ?_⟩
    · intro u v huv
      apply hrows u v
      simp [addRow, huv]
    · apply hrows a b
      simp [addRow]
  · rintro ⟨⟨hlist, hrows⟩, hab⟩
    refine ⟨hlist, ?_⟩
    intro u v huv
    have hor : S.edge u v = true ∨ (u = a ∧ v = b) := by
      simpa [addRow] using huv
    rcases hor with hold | ⟨rfl, rfl⟩
    · exact hrows u v hold
    · exact hab

theorem maps_addRow (S : WeakSystem α K) (a b : α) :
    (S.addRow a b).maps = S.maps.filter (fun f => f a ≤ f b) := by
  ext f
  simp

/-- The two weak comparison branches cover the parent, including ties. -/
theorem branches_cover (S : WeakSystem α K) (a b : α) :
    (S.addRow a b).maps ∪ (S.addRow b a).maps = S.maps := by
  ext f
  simp only [Finset.mem_union, mem_maps, valid_addRow]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases le_total (f a) (f b) with hab | hba
    · exact Or.inl ⟨h, hab⟩
    · exact Or.inr ⟨h, hba⟩

/-- Their overlap consists exactly of tied colours. -/
theorem branches_inter (S : WeakSystem α K) (a b : α) :
    (S.addRow a b).maps ∩ (S.addRow b a).maps =
      S.maps.filter (fun f => f a = f b) := by
  ext f
  simp only [Finset.mem_inter, mem_maps, valid_addRow, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h, hab⟩, ⟨_, hba⟩⟩
    exact ⟨h, le_antisymm hab hba⟩
  · rintro ⟨h, heq⟩
    exact ⟨⟨h, heq.le⟩, ⟨h, heq.ge⟩⟩

/-- The sum of the child counts counts ties twice, not once. -/
theorem branch_count_identity (S : WeakSystem α K) (a b : α) :
    (S.addRow a b).count + (S.addRow b a).count =
      S.count + (S.maps.filter (fun f => f a = f b)).card := by
  simpa only [count, branches_cover, branches_inter] using
    (Finset.card_union_add_card_inter (S.addRow a b).maps (S.addRow b a).maps).symm

theorem parent_count_le_sum (S : WeakSystem α K) (a b : α) :
    S.count ≤ (S.addRow a b).count + (S.addRow b a).count := by
  rw [branch_count_identity]
  omega

/-- The exact counting rule, with a deterministic tie in favour of `a ≤ b`. -/
def choose (S : WeakSystem α K) (a b : α) : WeakSystem α K :=
  if (S.addRow b a).count ≤ (S.addRow a b).count then
    S.addRow a b
  else S.addRow b a

/-- An exact larger branch retains at least half the parent count. -/
theorem count_le_twice_choose (S : WeakSystem α K) (a b : α) :
    S.count ≤ 2 * (S.choose a b).count := by
  have hsum := S.parent_count_le_sum a b
  unfold choose
  split_ifs with h
  · omega
  · omega

theorem choose_count_pos (S : WeakSystem α K) (a b : α) (h : 0 < S.count) :
    0 < (S.choose a b).count := by
  have := S.count_le_twice_choose a b
  omega

theorem choose_has_map (S : WeakSystem α K) (a b : α) (h : ∃ f, S.Valid f) :
    ∃ f, (S.choose a b).Valid f := by
  exact (count_pos_iff _).mp (S.choose_count_pos a b ((count_pos_iff _).mpr h))

theorem maps_addRow_subset (S : WeakSystem α K) (a b : α) :
    (S.addRow a b).maps ⊆ S.maps := by
  intro f hf
  exact (mem_maps S f).mpr
    ((valid_addRow S a b f).mp ((mem_maps (S.addRow a b) f).mp hf)).1

theorem maps_choose_subset (S : WeakSystem α K) (a b : α) :
    (S.choose a b).maps ⊆ S.maps := by
  unfold choose
  split_ifs <;> exact maps_addRow_subset _ _ _

/-- An exact colour fiber, before any palette refinement. -/
def fiber (S : WeakSystem α K) (v : α) (c : Fin K) : Finset (ColorMap α K) :=
  S.maps.filter (fun f => f v = c)

@[simp] theorem mem_fiber (S : WeakSystem α K) (v : α) (c : Fin K)
    (f : ColorMap α K) : f ∈ S.fiber v c ↔ S.Valid f ∧ f v = c := by
  simp [fiber]

theorem fiber_subset_maps (S : WeakSystem α K) (v : α) (c : Fin K) :
    S.fiber v c ⊆ S.maps := Finset.filter_subset _ _

/-- An independent admission has one extension for every allowed new colour.
This is the finite product identity underlying the daughter birth credit. -/
theorem independent_birth_count (S : WeakSystem α K) (L : ℕ) :
    (S.maps ×ˢ (Finset.univ : Finset (Fin L))).card = S.count * L := by
  simp [count]

end Finite

section Windows

variable [Fintype α]

/-- The hypotheses required when the stored rows already include their
reflexive transitive closure.  No antisymmetry is required for weak maps. -/
structure Closed (S : WeakSystem α K) : Prop where
  refl : ∀ v, S.edge v v = true
  trans : ∀ u v w, S.edge u v = true → S.edge v w = true → S.edge u w = true

/-- The largest list floor among the predecessors, including the label itself
when `Closed` holds. -/
def effectiveLower (S : WeakSystem α (K + 1)) (v : α) : Fin (K + 1) :=
  Finset.univ.sup (fun u => if S.edge u v = true then S.lower u else ⊥)

/-- The smallest list ceiling among the successors, including the label itself
when `Closed` holds. -/
def effectiveUpper (S : WeakSystem α (K + 1)) (v : α) : Fin (K + 1) :=
  Finset.univ.inf (fun u => if S.edge v u = true then S.upper u else ⊤)

theorem lower_le_effectiveLower (S : WeakSystem α (K + 1))
    {u v : α} (h : S.edge u v = true) : S.lower u ≤ S.effectiveLower v := by
  simpa [effectiveLower, h] using
    (Finset.le_sup (s := (Finset.univ : Finset α))
      (f := fun w => if S.edge w v = true then S.lower w else ⊥)
      (Finset.mem_univ u))

theorem effectiveUpper_le_upper (S : WeakSystem α (K + 1))
    {u v : α} (h : S.edge u v = true) : S.effectiveUpper u ≤ S.upper v := by
  simpa [effectiveUpper, h] using
    (Finset.inf_le (s := (Finset.univ : Finset α))
      (f := fun w => if S.edge u w = true then S.upper w else ⊤)
      (Finset.mem_univ v))

/-- Every valid map lies between the propagated bounds. -/
theorem valid_between_windows (S : WeakSystem α (K + 1)) (f : ColorMap α (K + 1))
    (hf : S.Valid f) (v : α) :
    S.effectiveLower v ≤ f v ∧ f v ≤ S.effectiveUpper v := by
  constructor
  · apply Finset.sup_le
    intro u _
    split_ifs with h
    · exact le_trans (hf.1 u).1 (hf.2 u v h)
    · exact bot_le
  · apply Finset.le_inf
    intro u _
    split_ifs with h
    · exact le_trans (hf.2 v u h) (hf.1 u).2
    · exact le_top

theorem effectiveLower_mono (S : WeakSystem α (K + 1)) (hS : S.Closed)
    {u v : α} (huv : S.edge u v = true) :
    S.effectiveLower u ≤ S.effectiveLower v := by
  apply Finset.sup_le
  intro w _
  split_ifs with hwu
  · exact S.lower_le_effectiveLower (hS.trans w u v hwu huv)
  · exact bot_le

theorem effectiveUpper_mono (S : WeakSystem α (K + 1)) (hS : S.Closed)
    {u v : α} (huv : S.edge u v = true) :
    S.effectiveUpper u ≤ S.effectiveUpper v := by
  apply Finset.le_inf
  intro w _
  split_ifs with hvw
  · exact S.effectiveUpper_le_upper (hS.trans u v w huv hvw)
  · exact le_top

/-- Noncrossing propagated bounds give a concrete least feasible assignment. -/
theorem effectiveLower_valid (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (hw : ∀ v, S.effectiveLower v ≤ S.effectiveUpper v) :
    S.Valid S.effectiveLower := by
  constructor
  · intro v
    exact ⟨S.lower_le_effectiveLower (hS.refl v),
      le_trans (hw v) (S.effectiveUpper_le_upper (hS.refl v))⟩
  · intro u v huv
    exact S.effectiveLower_mono hS huv

/-- The dual endpoint assignment is feasible too. -/
theorem effectiveUpper_valid (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (hw : ∀ v, S.effectiveLower v ≤ S.effectiveUpper v) :
    S.Valid S.effectiveUpper := by
  constructor
  · intro v
    exact ⟨le_trans (S.lower_le_effectiveLower (hS.refl v)) (hw v),
      S.effectiveUpper_le_upper (hS.refl v)⟩
  · intro u v huv
    exact S.effectiveUpper_mono hS huv

/-- Feasibility is exactly the absence of a crossed effective window. -/
theorem feasible_iff_windows (S : WeakSystem α (K + 1)) (hS : S.Closed) :
    (∃ f, S.Valid f) ↔ ∀ v, S.effectiveLower v ≤ S.effectiveUpper v := by
  constructor
  · rintro ⟨f, hf⟩ v
    exact le_trans (S.valid_between_windows f hf v).1
      (S.valid_between_windows f hf v).2
  · intro hw
    exact ⟨S.effectiveLower, S.effectiveLower_valid hS hw⟩

/-- The least endpoint assignment with the proposed value propagated upward
from one label. -/
def extendValue (S : WeakSystem α (K + 1)) (v : α) (c : Fin (K + 1)) :
    ColorMap α (K + 1) :=
  fun w => max (S.effectiveLower w) (if S.edge v w = true then c else ⊥)

theorem extendValue_valid (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (hw : ∀ w, S.effectiveLower w ≤ S.effectiveUpper w)
    (v : α) (c : Fin (K + 1)) (hc : c ≤ S.effectiveUpper v) :
    S.Valid (S.extendValue v c) := by
  have hleast := S.effectiveLower_valid hS hw
  constructor
  · intro w
    constructor
    · exact le_trans (hleast.1 w).1 (le_max_left _ _)
    · apply max_le
      · exact (hleast.1 w).2
      · split_ifs with hvw
        · exact le_trans hc (S.effectiveUpper_le_upper hvw)
        · exact bot_le
  · intro u w huw
    apply max_le_max (S.effectiveLower_mono hS huw)
    by_cases hvu : S.edge v u = true
    · simp [hvu, hS.trans v u w hvu huw]
    · simp [hvu]

theorem extendValue_at (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (v : α) (c : Fin (K + 1)) (hc : S.effectiveLower v ≤ c) :
    S.extendValue v c v = c := by
  simp [extendValue, hS.refl v, max_eq_right hc]

/-- Every integer in an effective window is attainable; there are no gaps in
the support of a feasible label. -/
theorem support_iff_window (S : WeakSystem α (K + 1)) (hS : S.Closed)
    (hfeas : ∃ f, S.Valid f) (v : α) (c : Fin (K + 1)) :
    (∃ f, S.Valid f ∧ f v = c) ↔
      S.effectiveLower v ≤ c ∧ c ≤ S.effectiveUpper v := by
  constructor
  · rintro ⟨f, hf, hfc⟩
    simpa [hfc] using S.valid_between_windows f hf v
  · rintro ⟨hl, hu⟩
    exact ⟨S.extendValue v c,
      S.extendValue_valid hS ((S.feasible_iff_windows hS).mp hfeas) v c hu,
      S.extendValue_at hS v c hl⟩

end Windows

section Enlargement

variable [Fintype α] [DecidableEq α]

/-- Append one unused top colour, retaining every old list endpoint exactly.
Even an old full list keeps its old upper bound. -/
def enlarge (S : WeakSystem α K) : WeakSystem α (K + 1) where
  edge := S.edge
  lower v := (S.lower v).castSucc
  upper v := (S.upper v).castSucc

/-- The coordinatewise inclusion of an old palette into the enlarged one. -/
def paletteEmbedding : ColorMap α K ↪ ColorMap α (K + 1) where
  toFun f v := (f v).castSucc
  inj' := by
    intro f g h
    funext v
    exact Fin.castSucc_inj.mp (congrFun h v)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem valid_enlarge_embedding (S : WeakSystem α K) (f : ColorMap α K) :
    S.enlarge.Valid (paletteEmbedding f) ↔ S.Valid f := Iff.rfl

/-- The new palette creates no new assignment of old labels.  The unchanged
old ceilings rule out the newly appended colour at every old coordinate. -/
theorem maps_enlarge (S : WeakSystem α K) :
    S.enlarge.maps = S.maps.map paletteEmbedding := by
  ext f
  constructor
  · intro hf
    have hf' : S.enlarge.Valid f := (mem_maps _ _).mp hf
    let g : ColorMap α K := fun v =>
      ⟨(f v).val, lt_of_le_of_lt (hf'.1 v).2 (S.upper v).isLt⟩
    have hg : S.Valid g := by
      constructor
      · intro v
        exact hf'.1 v
      · intro u v huv
        exact hf'.2 u v huv
    apply Finset.mem_map.mpr
    refine ⟨g, (mem_maps S g).mpr hg, ?_⟩
    funext v
    apply Fin.ext
    rfl
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hf
    exact (mem_maps _ _).mpr
      ((valid_enlarge_embedding S g).mpr ((mem_maps S g).mp hg))

theorem count_enlarge (S : WeakSystem α K) : S.enlarge.count = S.count := by
  simp [count, maps_enlarge]

omit [Fintype α] in
@[simp] theorem enlarge_addRow (S : WeakSystem α K) (a b : α) :
    (S.addRow a b).enlarge = S.enlarge.addRow a b := rfl

end Enlargement

section Birth

variable [Fintype α] [DecidableEq α]

/-- Admit one new, unrelated label with the full current palette.  The new
label is `none`; old labels are `some v`.  All old lists remain unchanged. -/
def birth (S : WeakSystem α (K + 1)) : WeakSystem (Option α) (K + 1) where
  edge u v := match u, v with
    | some a, some b => S.edge a b
    | _, _ => false
  lower v := match v with
    | none => ⊥
    | some a => S.lower a
  upper v := match v with
    | none => ⊤
    | some a => S.upper a

omit [Fintype α] [DecidableEq α] in
@[simp] theorem valid_birth (S : WeakSystem α (K + 1))
    (f : ColorMap (Option α) (K + 1)) :
    S.birth.Valid f ↔ S.Valid (fun a => f (some a)) := by
  constructor
  · intro hf
    constructor
    · intro a
      exact hf.1 (some a)
    · intro a b hab
      exact hf.2 (some a) (some b) hab
  · intro hf
    constructor
    · intro v
      cases v with
      | none => exact ⟨bot_le, le_top⟩
      | some a => exact hf.1 a
    · intro u v huv
      cases u with
      | none => simp [birth] at huv
      | some a =>
          cases v with
          | none => simp [birth] at huv
          | some b => exact hf.2 a b huv

/-- Assemble an old map and the colour of the newly admitted label. -/
def freshEmbedding : ColorMap α K × Fin K ↪ ColorMap (Option α) K where
  toFun p v := match v with
    | none => p.2
    | some a => p.1 a
  inj' := by
    intro p q h
    apply Prod.ext
    · funext a
      exact congrFun h (some a)
    · exact congrFun h none

/-- Fresh admission is exactly a Cartesian product, not merely a bound on
cardinalities.  This uses the absence of old rows incident to the new label. -/
theorem maps_birth (S : WeakSystem α (K + 1)) :
    S.birth.maps = (S.maps ×ˢ (Finset.univ : Finset (Fin (K + 1)))).map freshEmbedding := by
  ext f
  constructor
  · intro hf
    apply Finset.mem_map.mpr
    refine ⟨(fun a => f (some a), f none), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      exact ⟨(mem_maps S _).mpr ((valid_birth S f).mp ((mem_maps _ _).mp hf)),
        Finset.mem_univ _⟩
    · funext v
      cases v <;> rfl
  · intro hf
    obtain ⟨⟨g, c⟩, hpair, rfl⟩ := Finset.mem_map.mp hf
    apply (mem_maps _ _).mpr
    apply (valid_birth _ _).mpr
    exact (mem_maps S g).mp (Finset.mem_product.mp hpair).1

/-- Each old map gains one independent extension per available colour. -/
theorem count_birth (S : WeakSystem α (K + 1)) :
    S.birth.count = S.count * (K + 1) := by
  simp [count, maps_birth]

/-- In particular the `j`th birth earns a factor of at least `j` whenever the
current palette has at least `j` colours. -/
theorem birth_credit (S : WeakSystem α (K + 1)) {j : ℕ} (hj : j ≤ K + 1) :
    j * S.count ≤ S.birth.count := by
  rw [count_birth, Nat.mul_comm S.count]
  exact Nat.mul_le_mul_right S.count hj

/-- A top-colour size repair followed by an independent admission leaves the
old law intact and earns the entire new palette as a birth factor. -/
theorem count_enlarge_birth (S : WeakSystem α K) :
    S.enlarge.birth.count = S.count * (K + 1) := by
  rw [count_birth, count_enlarge]

theorem enlarge_birth_credit (S : WeakSystem α K) {j : ℕ} (hj : j ≤ K + 1) :
    j * S.count ≤ S.enlarge.birth.count := by
  rw [count_enlarge_birth, Nat.mul_comm S.count]
  exact Nat.mul_le_mul_right S.count hj

end Birth
end WeakSystem
end SortingAdversary.Optimal.WeakMaps
