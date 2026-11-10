import Mathlib.Logic.Relation
import SortingAdversary.Continuous.Density
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Reversible component swaps for strictly ordered real maps

Two real maps determine a graph from their unordered coordinate pairs.
Swapping the maps on one connected component preserves that graph, making
the swap an involution.  If both maps respect the generating relation, the
swap preserves their strict inequalities.  A strict inequality at the marked
vertex propagates throughout its component and controls the unary walls.
-/

namespace SortingAdversary.Continuous.ComponentSwap

open MeasureTheory Set

variable {α : Type*}

def Along (r : α → α → Prop) (f : α → ℝ) : Prop :=
  ∀ u v, r u v → f u < f v

/-- An undirected edge joins two coordinate pairs when independent choices
from those pairs could violate a generating strict inequality. -/
def Linked (r : α → α → Prop) (f g : α → ℝ) (u v : α) : Prop :=
  (r u v ∧ min (f v) (g v) ≤ max (f u) (g u)) ∨
    (r v u ∧ min (f u) (g u) ≤ max (f v) (g v))

def Component (r : α → α → Prop) (root : α) (f g : α → ℝ) (x : α) : Prop :=
  Relation.ReflTransGen (Linked r f g) root x

theorem root_mem (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    Component r root f g root := .refl

theorem linked_symm {r : α → α → Prop} {f g : α → ℝ} {u v : α}
    (h : Linked r f g u v) : Linked r f g v u := Or.symm h

noncomputable def first (r : α → α → Prop) (root : α) (f g : α → ℝ) : α → ℝ := by
  classical
  exact fun x => if Component r root f g x then g x else f x

noncomputable def second (r : α → α → Prop) (root : α) (f g : α → ℝ) : α → ℝ := by
  classical
  exact fun x => if Component r root f g x then f x else g x

@[simp] theorem first_root (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    first r root f g root = g root := by
  simp [first, root_mem]

@[simp] theorem second_root (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    second r root f g root = f root := by
  simp [second, root_mem]

theorem max_swap (r : α → α → Prop) (root : α) (f g : α → ℝ) (x : α) :
    max (first r root f g x) (second r root f g x) = max (f x) (g x) := by
  classical
  by_cases hx : Component r root f g x <;> simp [first, second, hx, max_comm]

theorem min_swap (r : α → α → Prop) (root : α) (f g : α → ℝ) (x : α) :
    min (first r root f g x) (second r root f g x) = min (f x) (g x) := by
  classical
  by_cases hx : Component r root f g x <;> simp [first, second, hx, min_comm]

theorem linked_swap (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    Linked r (first r root f g) (second r root f g) = Linked r f g := by
  funext u v
  apply propext
  simp only [Linked, min_swap, max_swap]

theorem component_swap (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    Component r root (first r root f g) (second r root f g) = Component r root f g := by
  unfold Component
  rw [linked_swap]

theorem first_twice (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    first r root (first r root f g) (second r root f g) = f := by
  classical
  funext x
  simp only [first, component_swap]
  by_cases hx : Component r root f g x <;> simp [second, hx]

theorem second_twice (r : α → α → Prop) (root : α) (f g : α → ℝ) :
    second r root (first r root f g) (second r root f g) = g := by
  classical
  funext x
  simp only [second, component_swap]
  by_cases hx : Component r root f g x <;> simp [first, hx]

/-- The same component can be reconstructed from the outputs. -/
theorem recover {r : α → α → Prop} {root : α} {f g f' g' : α → ℝ}
    (hfirst : first r root f g = first r root f' g')
    (hsecond : second r root f g = second r root f' g') : f = f' ∧ g = g' := by
  constructor
  · calc
      f = first r root (first r root f g) (second r root f g) := (first_twice _ _ _ _).symm
      _ = first r root (first r root f' g') (second r root f' g') := by rw [hfirst, hsecond]
      _ = f' := first_twice _ _ _ _
  · calc
      g = second r root (first r root f g) (second r root f g) := (second_twice _ _ _ _).symm
      _ = second r root (first r root f' g') (second r root f' g') := by rw [hfirst, hsecond]
      _ = g' := second_twice _ _ _ _

private theorem strict_sign (a b c d : ℝ) (hac : a < c) (hbd : b < d)
    (hcross : min c d ≤ max a b) : a < b ↔ c < d := by
  simp only [min_def, max_def] at hcross
  split_ifs at hcross <;> constructor <;> intro h <;> linarith

theorem linked_strict {r : α → α → Prop} {f g : α → ℝ}
    (hf : Along r f) (hg : Along r g) {u v : α} (h : Linked r f g u v) :
    f u < g u ↔ f v < g v := by
  rcases h with ⟨huv, hcross⟩ | ⟨hvu, hcross⟩
  · exact strict_sign _ _ _ _ (hf u v huv) (hg u v huv) hcross
  · exact (strict_sign _ _ _ _ (hf v u hvu) (hg v u hvu) hcross).symm

theorem component_strict {r : α → α → Prop} {root : α} {f g : α → ℝ}
    (hf : Along r f) (hg : Along r g) (hroot : f root < g root) {x : α}
    (hx : Component r root f g x) : f x < g x := by
  induction hx with
  | refl => exact hroot
  | tail _ hlink ih => exact (linked_strict hf hg hlink).mp ih

/-- Cross-component edges allow all four choices from the two coordinate
pairs.  Within one component both ends are swapped together. -/
theorem along_swapped {r : α → α → Prop} {root : α} {f g : α → ℝ}
    (hf : Along r f) (hg : Along r g) :
    Along r (first r root f g) ∧ Along r (second r root f g) := by
  classical
  suffices h : ∀ u v, r u v →
      first r root f g u < first r root f g v ∧
        second r root f g u < second r root f g v from
    ⟨fun u v huv => (h u v huv).1, fun u v huv => (h u v huv).2⟩
  intro u v huv
  by_cases hu : Component r root f g u
  · by_cases hv : Component r root f g v
    · simpa [first, second, hu, hv] using ⟨hg u v huv, hf u v huv⟩
    · have hcross : max (f u) (g u) < min (f v) (g v) := by
        by_contra h
        exact hv (hu.tail (Or.inl ⟨huv, le_of_not_gt h⟩))
      simp only [first, second, if_pos hu, if_neg hv]
      exact ⟨(le_max_right (f u) (g u)).trans_lt (hcross.trans_le (min_le_left (f v) (g v))),
        (le_max_left (f u) (g u)).trans_lt (hcross.trans_le (min_le_right (f v) (g v)))⟩
  · by_cases hv : Component r root f g v
    · have hcross : max (f u) (g u) < min (f v) (g v) := by
        by_contra h
        exact hu (hv.tail (Or.inr ⟨huv, le_of_not_gt h⟩))
      simp only [first, second, if_neg hu, if_pos hv]
      exact ⟨(le_max_left (f u) (g u)).trans_lt (hcross.trans_le (min_le_right (f v) (g v))),
        (le_max_right (f u) (g u)).trans_lt (hcross.trans_le (min_le_left (f v) (g v)))⟩
    · simpa [first, second, hu, hv] using ⟨hf u v huv, hg u v huv⟩

/-- On the selected component, `f < g` leaves room for the nonnegative translation.
The original maps are `f` and `g+δ`; the outputs are the first swap and the
second swap plus `δ`. -/
theorem walls_swapped {r : α → α → Prop} {root : α} {f g L U : α → ℝ}
    (hf : Along r f) (hg : Along r g) (hroot : f root < g root)
    {δ : ℝ} (hδ : 0 ≤ δ) (hfwall : ∀ x, L x < f x ∧ f x < U x)
    (hgwall : ∀ x, L x < g x + δ ∧ g x + δ < U x) (x : α) :
    (L x < first r root f g x ∧ first r root f g x < U x) ∧
      (L x < second r root f g x + δ ∧ second r root f g x + δ < U x) := by
  classical
  have hfw := hfwall x
  have hgw := hgwall x
  by_cases hx : Component r root f g x
  · have hstrict := component_strict hf hg hroot hx
    simp only [first, second, if_pos hx]
    constructor <;> constructor <;> linarith
  · simpa only [first, second, if_neg hx] using ⟨hfw, hgw⟩

section Measurability

variable [Fintype α] {β : Type*} [MeasurableSpace β]

theorem linked_measurable (r : α → α → Prop) (f g : β → α → ℝ)
    (hf : ∀ x, Measurable (fun z => f z x)) (hg : ∀ x, Measurable (fun z => g z x))
    (u v : α) : MeasurableSet {z | Linked r (f z) (g z) u v} := by
  exact ((MeasurableSet.const (r u v)).inter
    (measurableSet_le ((hf v).min (hg v)) ((hf u).max (hg u)))).union
    ((MeasurableSet.const (r v u)).inter
      (measurableSet_le ((hf u).min (hg u)) ((hf v).max (hg v))))

/-- Reachability is measurable because it depends on a finite graph of
measurable comparisons. No bound on the length of a witnessing walk is needed. -/
theorem component_measurable (r : α → α → Prop) (root : α) (f g : β → α → ℝ)
    (hf : ∀ x, Measurable (fun z => f z x)) (hg : ∀ x, Measurable (fun z => g z x))
    (x : α) : MeasurableSet {z | Component r root (f z) (g z) x} := by
  let graph (z : β) : Set (α × α) := {uv | Linked r (f z) (g z) uv.1 uv.2}
  have hm : Measurable graph := measurable_set_iff.mpr
    (fun uv => measurableSet_setOfPred.mp (linked_measurable r f g hf hg uv.1 uv.2))
  let reach (G : Set (α × α)) : Prop :=
    Relation.ReflTransGen (fun u v => (u, v) ∈ G) root x
  have hr : Measurable reach := measurable_of_countable _
  exact measurableSet_setOfPred.mpr (hr.comp hm)

noncomputable def componentSet (r : α → α → Prop) (root : α) (f g : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (Component r root f g)

@[simp] theorem mem_componentSet (r : α → α → Prop) (root : α) (f g : α → ℝ) (x : α) :
    x ∈ componentSet r root f g ↔ Component r root f g x := by
  classical
  simp [componentSet]

theorem componentSet_measurable (r : α → α → Prop) (root : α) (f g : β → α → ℝ)
    (hf : ∀ x, Measurable (fun z => f z x)) (hg : ∀ x, Measurable (fun z => g z x)) :
    Measurable (fun z => componentSet r root (f z) (g z)) := by
  rw [measurable_finset_iff]
  intro x
  apply measurableSet_setOfPred.mp
  simpa only [mem_componentSet] using component_measurable r root f g hf hg x

end Measurability

end SortingAdversary.Continuous.ComponentSwap
