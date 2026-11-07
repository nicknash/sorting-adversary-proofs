import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int

/-!
# Integer compression before inserting one label

The order used in this file is the transitively closed public order. A valid
colour assignment respects it weakly. Floors and ceilings have already been
propagated, so each is a monotone function of the label.

For a deleted label with interval `[L,U]`, compress its proper predecessors
towards `L` and its proper successors towards `U`, by integer division by four.
Other coordinates are unchanged. This is an explicit map, not a postulated
compression operation. The proofs below check its ranges, walls and order.
-/

namespace SortingAdversary.Optimal.Insertion

/-- Compress values above `L` towards `L`, fixing the values below `L`. -/
def compressDown (L x : ℤ) : ℤ :=
  if x < L then x else L + (x - L) / 4

/-- The reflected compression towards `U`, fixing values above `U`. -/
def compressUp (U x : ℤ) : ℤ :=
  if U < x then x else U - (U - x) / 4

theorem compressDown_le (L x : ℤ) : compressDown L x ≤ x := by
  unfold compressDown
  split <;> omega

theorem le_compressUp (U x : ℤ) : x ≤ compressUp U x := by
  unfold compressUp
  split <;> omega

theorem compressDown_monotone (L : ℤ) : Monotone (compressDown L) := by
  intro x y hxy
  unfold compressDown
  split <;> split <;> omega

theorem compressUp_monotone (U : ℤ) : Monotone (compressUp U) := by
  intro x y hxy
  unfold compressUp
  split <;> split <;> omega

theorem floor_le_compressDown {a L x : ℤ} (haL : a ≤ L) (hax : a ≤ x) :
    a ≤ compressDown L x := by
  unfold compressDown
  split <;> omega

theorem compressUp_le_ceiling {b U x : ℤ} (hUb : U ≤ b) (hxb : x ≤ b) :
    compressUp U x ≤ b := by
  unfold compressUp
  split <;> omega

theorem compressDown_le_inner {L U x : ℤ} (hLU : L ≤ U) (hxU : x ≤ U) :
    compressDown L x ≤ L + (U - L) / 4 := by
  unfold compressDown
  split <;> omega

theorem inner_le_compressUp {L U x : ℤ} (hLU : L ≤ U) (hLx : L ≤ x) :
    U - (U - L) / 4 ≤ compressUp U x := by
  unfold compressUp
  split <;> omega

/-- The central interval is nonempty, including intervals of width one. -/
theorem inner_interval_nonempty {L U : ℤ} (hLU : L ≤ U) :
    L + (U - L) / 4 ≤ U - (U - L) / 4 := by
  omega

/-- The central interval remains inside the original propagated window. -/
theorem inner_interval_subset {L U t : ℤ} (hLU : L ≤ U)
    (htL : L + (U - L) / 4 ≤ t) (htU : t ≤ U - (U - L) / 4) :
    L ≤ t ∧ t ≤ U := by
  constructor <;> omega

/-- The two lost low bits of an integer division by four. -/
def quarterResidue (z : ℤ) : Fin 4 :=
  ⟨(z % 4).toNat, by omega⟩

theorem emod_eq_of_quarterResidue_eq {x y : ℤ}
    (h : quarterResidue x = quarterResidue y) : x % 4 = y % 4 := by
  have hv := congrArg Fin.val h
  simp only [quarterResidue] at hv
  omega

/-- A compressed value and one of four residue codes recover its predecessor. -/
theorem compressDown_recover {L x y : ℤ}
    (hvalue : compressDown L x = compressDown L y)
    (hcode : quarterResidue (x - L) = quarterResidue (y - L)) : x = y := by
  have hmod := emod_eq_of_quarterResidue_eq hcode
  unfold compressDown at hvalue
  split at hvalue <;> split at hvalue <;> omega

theorem compressUp_recover {U x y : ℤ}
    (hvalue : compressUp U x = compressUp U y)
    (hcode : quarterResidue (U - x) = quarterResidue (U - y)) : x = y := by
  have hmod := emod_eq_of_quarterResidue_eq hcode
  unfold compressUp at hvalue
  split at hvalue <;> split at hvalue <;> omega

section OrderedLabels

variable {α : Type*} [PartialOrder α] [DecidableEq α] [DecidableLE α]

/-- A full weak assignment with inclusive unary walls. -/
def Valid (lower upper : α → ℤ) (f : α → ℤ) : Prop :=
  (∀ x, lower x ≤ f x ∧ f x ≤ upper x) ∧ Monotone f

/-- Delete `v`, retaining every transitive relation between remaining labels.
The unused value `f v` is ignored by this predicate. -/
def DeletedValid (v : α) (lower upper : α → ℤ) (f : α → ℤ) : Prop :=
  (∀ x, x ≠ v → lower x ≤ f x ∧ f x ≤ upper x) ∧
    ∀ x y, x ≠ v → y ≠ v → x ≤ y → f x ≤ f y

/-- The actual simultaneous compression followed by insertion at colour `t`.
The predecessor and successor cases are disjoint away from `v` by antisymmetry. -/
def compressedInsert (v : α) (L U t : ℤ) (f : α → ℤ) (x : α) : ℤ :=
  if x = v then t else
    if x ≤ v then compressDown L (f x) else
      if v ≤ x then compressUp U (f x) else f x

/-- The canonical representation of a deleted assignment. -/
def eraseAt (v : α) (f : α → ℤ) (x : α) : ℤ := if x = v then 0 else f x

omit [PartialOrder α] [DecidableLE α] in
theorem eraseAt_recover {v : α} {f g : α → ℤ}
    (hv : f v = g v) (herase : eraseAt v f = eraseAt v g) : f = g := by
  funext x
  by_cases hx : x = v
  · simpa [hx] using hv
  · have h := congrFun herase x
    simpa [eraseAt, hx] using h

omit [DecidableLE α] in
theorem deletedValid_eraseAt {v : α} {lower upper f : α → ℤ}
    (hf : Valid lower upper f) : DeletedValid v lower upper (eraseAt v f) := by
  constructor
  · intro x hx
    simpa [eraseAt, hx] using hf.1 x
  · intro x y hx hy hxy
    simpa [eraseAt, hx, hy] using hf.2 hxy

@[simp] theorem compressedInsert_at (v : α) (L U t : ℤ) (f : α → ℤ) :
    compressedInsert v L U t f v = t := by
  simp [compressedInsert]

/-- Every colour in the central interval is insertable after compression.
The proof covers all cross-edges to untouched coordinates as well as all unary
walls. It uses no counting oracle or probability assumption. -/
theorem compressedInsert_valid {v : α} {lower upper f : α → ℤ}
    (hlower : Monotone lower) (hupper : Monotone upper)
    (hwindow : lower v ≤ upper v) (hvalid : DeletedValid v lower upper f)
    {t : ℤ} (htL : lower v + (upper v - lower v) / 4 ≤ t)
    (htU : t ≤ upper v - (upper v - lower v) / 4) :
    Valid lower upper (compressedInsert v (lower v) (upper v) t f) := by
  have ht := inner_interval_subset hwindow htL htU
  constructor
  · intro x
    by_cases hx : x = v
    · simpa [hx] using ht
    · have hb := hvalid.1 x hx
      by_cases hxv : x ≤ v
      · simp only [compressedInsert, if_neg hx, if_pos hxv]
        exact ⟨floor_le_compressDown (hlower hxv) hb.1,
          (compressDown_le _ _).trans hb.2⟩
      · by_cases hvx : v ≤ x
        · simp only [compressedInsert, if_neg hx, if_neg hxv, if_pos hvx]
          exact ⟨hb.1.trans (le_compressUp _ _),
            compressUp_le_ceiling (hupper hvx) hb.2⟩
        · simpa only [compressedInsert, if_neg hx, if_neg hxv, if_neg hvx] using hb
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      by_cases hy : y = v
      · simp [hy]
      · have hyv : ¬ y ≤ v := fun hyv => hy (le_antisymm hyv hxy)
        have hl : lower v ≤ f y := (hlower hxy).trans (hvalid.1 y hy).1
        have hb := htU.trans (inner_le_compressUp hwindow hl)
        simpa [compressedInsert, hy, hyv, hxy] using hb
    · by_cases hy : y = v
      · subst y
        have hu : f x ≤ upper v := (hvalid.1 x hx).2.trans (hupper hxy)
        have hb := (compressDown_le_inner hwindow hu).trans htL
        simpa [compressedInsert, hx, hxy] using hb
      · have hfold := hvalid.2 x y hx hy hxy
        by_cases hxv : x ≤ v
        · by_cases hyv : y ≤ v
          · simpa only [compressedInsert, if_neg hx, if_neg hy, if_pos hxv, if_pos hyv]
              using compressDown_monotone (lower v) hfold
          · by_cases hvy : v ≤ y
            · simpa only [compressedInsert, if_neg hx, if_neg hy, if_pos hxv,
                if_neg hyv, if_pos hvy] using
                (compressDown_le _ _).trans (hfold.trans (le_compressUp _ _))
            · simpa only [compressedInsert, if_neg hx, if_neg hy, if_pos hxv,
                if_neg hyv, if_neg hvy] using (compressDown_le _ _).trans hfold
        · have hyv : ¬ y ≤ v := fun h => hxv (hxy.trans h)
          by_cases hvx : v ≤ x
          · have hvy : v ≤ y := hvx.trans hxy
            simpa only [compressedInsert, if_neg hx, if_neg hy, if_neg hxv,
              if_neg hyv, if_pos hvx, if_pos hvy] using
              compressUp_monotone (upper v) hfold
          · by_cases hvy : v ≤ y
            · simpa only [compressedInsert, if_neg hx, if_neg hy, if_neg hxv,
                if_neg hyv, if_neg hvx, if_pos hvy] using hfold.trans (le_compressUp _ _)
            · simpa only [compressedInsert, if_neg hx, if_neg hy, if_neg hxv,
                if_neg hyv, if_neg hvx, if_neg hvy] using hfold

/-- Only these proper comparable coordinates are altered by compression. -/
abbrev ComparableTo (v : α) := {x : α // x ≠ v ∧ (x ≤ v ∨ v ≤ x)}

/-- One four-valued code for each altered coordinate. -/
def insertionCode (v : α) (L U : ℤ) (f : α → ℤ) : ComparableTo v → Fin 4 :=
  fun x => if x.val ≤ v then quarterResidue (f x.val - L)
    else quarterResidue (U - f x.val)

/-- No source information is lost after retaining the small residue code.
The irrelevant deleted coordinate must have the same fixed dummy value. -/
theorem compressedInsert_recover {v : α} {L U t : ℤ} {f g : α → ℤ}
    (hv : f v = g v)
    (hvalue : compressedInsert v L U t f = compressedInsert v L U t g)
    (hcode : insertionCode v L U f = insertionCode v L U g) : f = g := by
  funext x
  by_cases hx : x = v
  · simpa [hx] using hv
  · have hout := congrFun hvalue x
    by_cases hxv : x ≤ v
    · have hc := congrFun hcode ⟨x, hx, Or.inl hxv⟩
      apply compressDown_recover
      · simpa only [compressedInsert, if_neg hx, if_pos hxv] using hout
      · simpa only [insertionCode, if_pos hxv] using hc
    · by_cases hvx : v ≤ x
      · have hc := congrFun hcode ⟨x, hx, Or.inr hvx⟩
        apply compressUp_recover
        · simpa only [compressedInsert, if_neg hx, if_neg hxv, if_pos hvx] using hout
        · simpa only [insertionCode, if_neg hxv] using hc
      · simpa only [compressedInsert, if_neg hx, if_neg hxv, if_neg hvx] using hout

section Finite

variable [Fintype α]

/-- All maps obtained from the source family at all proposed insertion colours. -/
def insertedMaps (v : α) (L U : ℤ) (S : Finset (α → ℤ)) (J : Finset ℤ) :
    Finset (α → ℤ) :=
  (S.product J).image (fun p => compressedInsert v L U p.2 p.1)

/-- Exact finite counting form of the `4^c` preimage bound, proved by coding.
The value at the inserted coordinate records the proposed colour, so colours
from `J` contribute disjoint images. -/
theorem card_mul_le_insertedMaps (v : α) (L U : ℤ)
    (S : Finset (α → ℤ)) (J : Finset ℤ)
    (hfixed : ∀ f ∈ S, f v = 0) :
    S.card * J.card ≤ (insertedMaps v L U S J).card *
      4 ^ Fintype.card (ComparableTo v) := by
  classical
  let imageFamily := insertedMaps v L U S J
  let encode : (S.product J) → imageFamily × (ComparableTo v → Fin 4) :=
    fun p => (⟨compressedInsert v L U p.val.2 p.val.1,
      Finset.mem_image_of_mem _ p.property⟩, insertionCode v L U p.val.1)
  have hinj : Function.Injective encode := by
    intro p q h
    have hmaps := congrArg (fun z : imageFamily × (ComparableTo v → Fin 4) => z.1.val) h
    have hcodes := congrArg Prod.snd h
    have ht : p.val.2 = q.val.2 := by
      have hv := congrFun hmaps v
      simpa only [encode, compressedInsert_at] using hv
    apply Subtype.ext
    apply Prod.ext
    · apply compressedInsert_recover
      · exact (hfixed p.val.1 (Finset.mem_product.mp p.property).1).trans
          (hfixed q.val.1 (Finset.mem_product.mp q.property).1).symm
      · simpa only [encode, ht] using hmaps
      · exact hcodes
    · exact ht
  have h := Fintype.card_le_of_injective encode hinj
  simpa [imageFamily, Fintype.card_fun] using h

/-- Counting against any explicit target family containing the insertions. -/
theorem card_mul_le_of_insertions_mem (v : α) (L U : ℤ)
    (S F : Finset (α → ℤ)) (J : Finset ℤ)
    (hfixed : ∀ f ∈ S, f v = 0)
    (hmem : ∀ f ∈ S, ∀ t ∈ J, compressedInsert v L U t f ∈ F) :
    S.card * J.card ≤ F.card * 4 ^ Fintype.card (ComparableTo v) := by
  have hsubset : insertedMaps v L U S J ⊆ F := by
    intro g hg
    obtain ⟨⟨f, t⟩, hp, rfl⟩ := Finset.mem_image.mp hg
    exact hmem f (Finset.mem_product.mp hp).1 t (Finset.mem_product.mp hp).2
  exact (card_mul_le_insertedMaps v L U S J hfixed).trans
    (Nat.mul_le_mul_right _ (Finset.card_le_card hsubset))

instance instDecidableValid (lower upper f : α → ℤ) :
    Decidable (Valid lower upper f) := by
  unfold Valid Monotone
  infer_instance

instance instDecidableDeletedValid (v : α) (lower upper f : α → ℤ) :
    Decidable (DeletedValid v lower upper f) := by
  unfold DeletedValid
  infer_instance

/-- Exhaustively enumerated full assignments. This definition is finite and
executable, but is not asserted to be a polynomial-time counting algorithm. -/
def fullMaps (lower upper : α → ℤ) : Finset (α → ℤ) :=
  (Fintype.piFinset (fun x => Finset.Icc (lower x) (upper x))).filter
    (Valid lower upper)

/-- Exhaustively enumerated deleted assignments, represented by setting the
unused coordinate to zero. This adds no restriction on a genuine free label. -/
def deletedMaps (v : α) (lower upper : α → ℤ) : Finset (α → ℤ) :=
  (Fintype.piFinset (fun x => if x = v then {0}
    else Finset.Icc (lower x) (upper x))).filter (DeletedValid v lower upper)

@[simp] theorem mem_fullMaps {lower upper f : α → ℤ} :
    f ∈ fullMaps lower upper ↔ Valid lower upper f := by
  simp only [fullMaps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

@[simp] theorem mem_deletedMaps {v : α} {lower upper f : α → ℤ} :
    f ∈ deletedMaps v lower upper ↔ f v = 0 ∧ DeletedValid v lower upper f := by
  simp only [deletedMaps, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hbox, hvalid⟩
    exact ⟨by simpa using hbox v, hvalid⟩
  · rintro ⟨hv, hvalid⟩
    refine ⟨?_, hvalid⟩
    intro x
    by_cases hx : x = v
    · simp [hx, hv]
    · simpa [hx] using hvalid.1 x hx

/-- The central insertion interval, counted with both endpoints included. -/
def centralColors (L U : ℤ) : Finset ℤ :=
  Finset.Icc (L + (U - L) / 4) (U - (U - L) / 4)

theorem width_le_twice_central_card {L U : ℤ} (hLU : L ≤ U) :
    (U - L + 1).toNat ≤ 2 * (centralColors L U).card := by
  simp only [centralColors, Int.card_Icc]
  omega

/-- The exact counting inequality from the manuscript, for explicitly
enumerated full and deleted weak maps: `|J| N₋ ≤ 4^c N`. -/
theorem deleted_count_mul_central_le_full {v : α} {lower upper : α → ℤ}
    (hlower : Monotone lower) (hupper : Monotone upper)
    (hwindow : lower v ≤ upper v) :
    (deletedMaps v lower upper).card * (centralColors (lower v) (upper v)).card ≤
      (fullMaps lower upper).card * 4 ^ Fintype.card (ComparableTo v) := by
  apply card_mul_le_of_insertions_mem v (lower v) (upper v)
  · intro f hf
    exact (mem_deletedMaps.mp hf).1
  · intro f hf t ht
    apply mem_fullMaps.mpr
    have hj := Finset.mem_Icc.mp ht
    exact compressedInsert_valid hlower hupper hwindow
      (mem_deletedMaps.mp hf).2 hj.1 hj.2

/-- Each *individual* central colour has at least a `4^c` fraction of the
deleted count. This is a finite count statement; division and probability
normalization can be done afterwards. -/
theorem deleted_count_le_central_fiber {v : α} {lower upper : α → ℤ}
    (hlower : Monotone lower) (hupper : Monotone upper)
    (hwindow : lower v ≤ upper v) {t : ℤ}
    (ht : t ∈ centralColors (lower v) (upper v)) :
    (deletedMaps v lower upper).card ≤
      ((fullMaps lower upper).filter (fun f => f v = t)).card *
        4 ^ Fintype.card (ComparableTo v) := by
  have h := card_mul_le_of_insertions_mem v (lower v) (upper v)
    (deletedMaps v lower upper)
    ((fullMaps lower upper).filter (fun f => f v = t)) {t}
    (fun f hf => (mem_deletedMaps.mp hf).1) (by
      intro f hf t' ht'
      have hteq : t' = t := Finset.mem_singleton.mp ht'
      subst t'
      apply Finset.mem_filter.mpr
      refine ⟨?_, compressedInsert_at _ _ _ _ _⟩
      apply mem_fullMaps.mpr
      have hj := Finset.mem_Icc.mp ht
      exact compressedInsert_valid hlower hupper hwindow
        (mem_deletedMaps.mp hf).2 hj.1 hj.2)
  simpa using h

/-- Deletion and the deleted colour together recover the full assignment.
There are only `W` choices for that colour. -/
theorem full_count_le_width_mul_deleted (v : α) (lower upper : α → ℤ) :
    (fullMaps lower upper).card ≤
      (upper v - lower v + 1).toNat * (deletedMaps v lower upper).card := by
  classical
  let window := Finset.Icc (lower v) (upper v)
  let encode : (fullMaps lower upper) → (deletedMaps v lower upper) × window :=
    fun f => (⟨eraseAt v f.val, mem_deletedMaps.mpr
      ⟨by simp [eraseAt], deletedValid_eraseAt (mem_fullMaps.mp f.property)⟩⟩,
      ⟨f.val v, Finset.mem_Icc.mpr ((mem_fullMaps.mp f.property).1 v)⟩)
  have hinj : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    apply eraseAt_recover (v := v)
    · exact congrArg (fun p : (deletedMaps v lower upper) × window => p.2.val) h
    · exact congrArg (fun p : (deletedMaps v lower upper) × window => p.1.val) h
  have h := Fintype.card_le_of_injective encode hinj
  have hwidth : (upper v + 1 - lower v).toNat = (upper v - lower v + 1).toNat := by
    congr 1
    omega
  simpa [window, Int.card_Icc, hwidth, Nat.mul_comm] using h

/-- The insertion lemma with the central interval eliminated:
`W N₋ ≤ 2 · 4^c · N`. No divisions or asymptotic notation are used. -/
theorem width_mul_deleted_count_le_twice_full {v : α} {lower upper : α → ℤ}
    (hlower : Monotone lower) (hupper : Monotone upper)
    (hwindow : lower v ≤ upper v) :
    (upper v - lower v + 1).toNat * (deletedMaps v lower upper).card ≤
      2 * 4 ^ Fintype.card (ComparableTo v) * (fullMaps lower upper).card := by
  have hw := width_le_twice_central_card hwindow
  have hc := deleted_count_mul_central_le_full hlower hupper hwindow
  calc
    (upper v - lower v + 1).toNat * (deletedMaps v lower upper).card ≤
        (2 * (centralColors (lower v) (upper v)).card) *
          (deletedMaps v lower upper).card := Nat.mul_le_mul_right _ hw
    _ = 2 * ((deletedMaps v lower upper).card *
          (centralColors (lower v) (upper v)).card) := by ac_rfl
    _ ≤ 2 * ((fullMaps lower upper).card *
          4 ^ Fintype.card (ComparableTo v)) := Nat.mul_le_mul_left 2 hc
    _ = _ := by ac_rfl

/-- Exact denominator-free version of the central point-mass lower bound:
`N ≤ W · 4^c · N_t`, hence `N_t/N ≥ 1/(W·4^c)` when the count is positive. -/
theorem full_count_le_central_fiber_mul {v : α} {lower upper : α → ℤ}
    (hlower : Monotone lower) (hupper : Monotone upper)
    (hwindow : lower v ≤ upper v) {t : ℤ}
    (ht : t ∈ centralColors (lower v) (upper v)) :
    (fullMaps lower upper).card ≤
      (upper v - lower v + 1).toNat * 4 ^ Fintype.card (ComparableTo v) *
        ((fullMaps lower upper).filter (fun f => f v = t)).card := by
  calc
    (fullMaps lower upper).card ≤
        (upper v - lower v + 1).toNat * (deletedMaps v lower upper).card :=
      full_count_le_width_mul_deleted v lower upper
    _ ≤ (upper v - lower v + 1).toNat *
        (((fullMaps lower upper).filter (fun f => f v = t)).card *
          4 ^ Fintype.card (ComparableTo v)) :=
      Nat.mul_le_mul_left _ (deleted_count_le_central_fiber hlower hupper hwindow ht)
    _ = _ := by ac_rfl

/-- Full assignments in which two distinct integer colours are within `z`.
The second coordinate may be dependent on the first through the public order. -/
def nearMaps (v w : α) (lower upper : α → ℤ) (z : ℕ) : Finset (α → ℤ) :=
  (fullMaps lower upper).filter (fun f => |f v - f w| ≤ (z : ℤ))

/-- Erasing `v` leaves at most `2z+1` possible offsets from the other label.
No independence assumption is made. -/
theorem near_count_le_deleted (v w : α) (hw : w ≠ v)
    (lower upper : α → ℤ) (z : ℕ) :
    (nearMaps v w lower upper z).card ≤
      (2 * z + 1) * (deletedMaps v lower upper).card := by
  classical
  let offsets := Finset.Icc (-(z : ℤ)) (z : ℤ)
  let encode : (nearMaps v w lower upper z) →
      (deletedMaps v lower upper) × offsets := fun f =>
    (⟨eraseAt v f.val, mem_deletedMaps.mpr
      ⟨by simp [eraseAt], deletedValid_eraseAt
        (mem_fullMaps.mp (Finset.mem_filter.mp f.property).1)⟩⟩,
      ⟨f.val v - f.val w,
        Finset.mem_Icc.mpr ((abs_le (a := f.val v - f.val w) (b := (z : ℤ))).mp
          (Finset.mem_filter.mp f.property).2)⟩)
  have hinj : Function.Injective encode := by
    intro f g h
    have herase := congrArg
      (fun p : (deletedMaps v lower upper) × offsets => p.1.val) h
    have hdelta := congrArg
      (fun p : (deletedMaps v lower upper) × offsets => p.2.val) h
    have hother : f.val w = g.val w := by
      have h := congrFun herase w
      simpa only [encode, eraseAt, if_neg hw] using h
    apply Subtype.ext
    apply eraseAt_recover (v := v)
    · change f.val v - f.val w = g.val v - g.val w at hdelta
      omega
    · exact herase
  have h := Fintype.card_le_of_injective encode hinj
  have hoffsets : offsets.card = 2 * z + 1 := by
    simp only [offsets, Int.card_Icc]
    omega
  simpa only [Fintype.card_prod, Fintype.card_coe, hoffsets, Nat.mul_comm] using h

/-- The discrete near-tie estimate in exact finite-count form:
`W · N_near ≤ 2 · 4^c · (2z+1) · N`.
This includes the tie event `z=0`. -/
theorem near_count_mul_width_le {v w : α} (hw : w ≠ v)
    {lower upper : α → ℤ} (hlower : Monotone lower) (hupper : Monotone upper)
    (hwindow : lower v ≤ upper v) (z : ℕ) :
    (nearMaps v w lower upper z).card * (upper v - lower v + 1).toNat ≤
      2 * 4 ^ Fintype.card (ComparableTo v) * (2 * z + 1) *
        (fullMaps lower upper).card := by
  calc
    (nearMaps v w lower upper z).card * (upper v - lower v + 1).toNat ≤
        ((2 * z + 1) * (deletedMaps v lower upper).card) *
          (upper v - lower v + 1).toNat :=
      Nat.mul_le_mul_right _ (near_count_le_deleted v w hw lower upper z)
    _ = (2 * z + 1) * ((upper v - lower v + 1).toNat *
          (deletedMaps v lower upper).card) := by ac_rfl
    _ ≤ (2 * z + 1) * (2 * 4 ^ Fintype.card (ComparableTo v) *
          (fullMaps lower upper).card) :=
      Nat.mul_le_mul_left _ (width_mul_deleted_count_le_twice_full hlower hupper hwindow)
    _ = _ := by ac_rfl

end Finite

end OrderedLabels

end SortingAdversary.Optimal.Insertion
