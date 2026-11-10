import SortingAdversary.Continuous.OrderRegion
import SortingAdversary.Continuous.RationalSemantics
import Mathlib.Data.List.Sort

/-!
# Correctness of the actual endpoint propagation passes

The forward pass makes lower endpoints monotone on every arc; the reverse
pass makes upper endpoints monotone and preserves the lower endpoints. The
only scheduling assumption is an explicit topological list containing every
vertex. Sorting by a strict rank computes such a list.
-/

namespace SortingAdversary.Continuous.OrderRegion

open FiniteAveraging

section OrderedField

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

@[simp] theorem lowerPass_edge (D : System ι K) (l : List ι) :
    (l.foldl propagateLower D).edge = D.edge := by
  induction l generalizing D with
  | nil => rfl
  | cons v l ih => exact ih (propagateLower D v)

@[simp] theorem lowerPass_upper (D : System ι K) (l : List ι) :
    (l.foldl propagateLower D).upper = D.upper := by
  induction l generalizing D with
  | nil => rfl
  | cons v l ih => exact ih (propagateLower D v)

@[simp] theorem upperPass_edge (D : System ι K) (l : List ι) :
    (l.foldl propagateUpper D).edge = D.edge := by
  induction l generalizing D with
  | nil => rfl
  | cons v l ih => exact ih (propagateUpper D v)

@[simp] theorem upperPass_lower (D : System ι K) (l : List ι) :
    (l.foldl propagateUpper D).lower = D.lower := by
  induction l generalizing D with
  | nil => rfl
  | cons v l ih => exact ih (propagateUpper D v)

theorem propagateLower_increases (D : System ι K) (v x : ι) :
    D.lower x ≤ (propagateLower D v).lower x := by
  by_cases hx : x = v
  · subst x
    simpa only [propagateLower, Function.update_self] using lower_le_conditionalLower D v D.lower
  · simp [propagateLower, Function.update_of_ne hx]

theorem propagateUpper_decreases (D : System ι K) (v x : ι) :
    (propagateUpper D v).upper x ≤ D.upper x := by
  by_cases hx : x = v
  · subst x
    simpa only [propagateUpper, Function.update_self] using conditionalUpper_le_upper D v D.upper
  · simp [propagateUpper, Function.update_of_ne hx]

theorem lowerPass_increases (D : System ι K) (l : List ι) (x : ι) :
    D.lower x ≤ (l.foldl propagateLower D).lower x := by
  induction l generalizing D with
  | nil => exact le_rfl
  | cons v l ih =>
    exact (propagateLower_increases D v x).trans (ih (propagateLower D v))

theorem upperPass_decreases (D : System ι K) (l : List ι) (x : ι) :
    (l.foldl propagateUpper D).upper x ≤ D.upper x := by
  induction l generalizing D with
  | nil => exact le_rfl
  | cons v l ih =>
    exact (ih (propagateUpper D v)).trans (propagateUpper_decreases D v x)

theorem lowerPass_fixed (D : System ι K) (l : List ι) (x : ι) (hx : x ∉ l) :
    (l.foldl propagateLower D).lower x = D.lower x := by
  induction l generalizing D with
  | nil => rfl
  | cons v l ih =>
    have hv : x ≠ v := fun heq => hx (List.mem_cons.mpr (Or.inl heq))
    have hl : x ∉ l := fun h => hx (List.mem_cons_of_mem _ h)
    change (l.foldl propagateLower (propagateLower D v)).lower x = _
    rw [ih (propagateLower D v) hl]
    simp [propagateLower, Function.update_of_ne hv]

theorem upperPass_fixed (D : System ι K) (l : List ι) (x : ι) (hx : x ∉ l) :
    (l.foldl propagateUpper D).upper x = D.upper x := by
  induction l generalizing D with
  | nil => rfl
  | cons v l ih =>
    have hv : x ≠ v := fun heq => hx (List.mem_cons.mpr (Or.inl heq))
    have hl : x ∉ l := fun h => hx (List.mem_cons_of_mem _ h)
    change (l.foldl propagateUpper (propagateUpper D v)).upper x = _
    rw [ih (propagateUpper D v) hl]
    simp [propagateUpper, Function.update_of_ne hv]

theorem lowerPass_normalized_targets (D : System ι K) (l : List ι)
    (htop : l.Pairwise (fun v w => D.edge w v = false)) :
    ∀ x y, D.edge x y = true → y ∈ l →
      (l.foldl propagateLower D).lower x ≤ (l.foldl propagateLower D).lower y := by
  induction l generalizing D with
  | nil => simp
  | cons v l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp htop
    intro x y hxy hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have hx : x ∉ l := by
        intro hx
        have := hhead x hx
        rw [this] at hxy
        contradiction
      change (l.foldl propagateLower (propagateLower D y)).lower x ≤
        (l.foldl propagateLower (propagateLower D y)).lower y
      rw [lowerPass_fixed _ l x hx]
      apply le_trans _ (lowerPass_increases (propagateLower D y) l y)
      by_cases he : x = y
      · subst x
        exact le_rfl
      · simp only [propagateLower, Function.update_of_ne he, Function.update_self]
        exact predecessor_le_conditionalLower D y x D.lower hxy
    · exact ih (propagateLower D v) htail x y hxy hy

theorem upperPass_normalized_sources (D : System ι K) (l : List ι)
    (htop : l.Pairwise (fun v w => D.edge v w = false)) :
    ∀ x y, D.edge x y = true → x ∈ l →
      (l.foldl propagateUpper D).upper x ≤ (l.foldl propagateUpper D).upper y := by
  induction l generalizing D with
  | nil => simp
  | cons v l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp htop
    intro x y hxy hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hy : y ∉ l := by
        intro hy
        have := hhead y hy
        rw [this] at hxy
        contradiction
      change (l.foldl propagateUpper (propagateUpper D x)).upper x ≤
        (l.foldl propagateUpper (propagateUpper D x)).upper y
      rw [upperPass_fixed _ l y hy]
      apply (upperPass_decreases (propagateUpper D x) l x).trans
      by_cases he : y = x
      · subst y
        exact le_rfl
      · simp only [propagateUpper, Function.update_self, Function.update_of_ne he]
        exact conditionalUpper_le_successor D x y D.upper hxy
    · exact ih (propagateUpper D v) htail x y hxy hx

@[simp] theorem normalize_edge (D : System ι K) (order : List ι) :
    (normalize D order).edge = D.edge := by simp only [normalize, upperPass_edge, lowerPass_edge]

/-- The two executable passes really produce canonical monotone bounds
when the supplied list is topological and contains every vertex. -/
theorem normalize_normalized (D : System ι K) (order : List ι)
    (hall : ∀ x, x ∈ order)
    (htop : order.Pairwise (fun v w => D.edge w v = false)) :
    Normalized (normalize D order) := by
  intro x y hxy
  rw [normalize_edge] at hxy
  constructor
  · simp only [normalize, upperPass_lower]
    exact lowerPass_normalized_targets D order htop x y hxy (hall y)
  · apply upperPass_normalized_sources (order.foldl propagateLower D) order.reverse
    · simpa only [lowerPass_edge, List.pairwise_reverse] using htop
    · simpa only [lowerPass_edge] using hxy
    · simpa using hall x

theorem normalize_widths_positive (D : System ι K) (order : List ι)
    (hne : ∃ X, D.StrictlyFeasible X) :
    ∀ x, (normalize D order).lower x < (normalize D order).upper x := by
  obtain ⟨X, hX⟩ := hne
  have h := (normalize_feasible_iff D order X).mpr hX
  exact fun x => (h.1 x).1.trans (h.1 x).2

theorem topological_of_rank (D : System ι K) (rank : ι → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (order : List ι) (hsorted : order.Pairwise (fun x y => rank x ≤ rank y)) :
    order.Pairwise (fun x y => D.edge y x = false) := by
  apply hsorted.imp
  intro x y hxy
  cases he : D.edge y x with
  | false => rfl
  | true => exact (Nat.not_lt_of_ge hxy (hrank y x he)).elim

end OrderedField

/-- Compute the normalization schedule by sorting the label enumeration
by any strict directed rank. Equal ranks are allowed at unrelated vertices. -/
def rankOrder {n : ℕ} (rank : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).mergeSort (fun x y => decide (rank x ≤ rank y))

@[simp] theorem mem_rankOrder {n : ℕ} (rank : Fin n → ℕ) (x : Fin n) :
    x ∈ rankOrder rank := by simp [rankOrder]

theorem rankOrder_sorted {n : ℕ} (rank : Fin n → ℕ) :
    (rankOrder rank).Pairwise (fun x y => rank x ≤ rank y) := by
  simpa only [rankOrder, decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun x y : Fin n => decide (rank x ≤ rank y))
    (fun x y z hxy hyz => by simpa using le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
    (fun x y => by simpa using le_total (rank x) (rank y)) (List.finRange n)

theorem rankOrder_nodup {n : ℕ} (rank : Fin n → ℕ) : (rankOrder rank).Nodup := by
  simpa only [rankOrder, List.nodup_mergeSort] using List.nodup_finRange n

theorem rankOrder_length {n : ℕ} (rank : Fin n → ℕ) : (rankOrder rank).length = n := by
  simp [rankOrder]

theorem normalize_rankOrder_normalized {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    Normalized (normalize D (rankOrder rank)) :=
  normalize_normalized D (rankOrder rank) (mem_rankOrder rank)
    (topological_of_rank D rank hrank _ (rankOrder_sorted rank))

end SortingAdversary.Continuous.OrderRegion
