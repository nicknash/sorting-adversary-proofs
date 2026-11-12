import SortingAdversary.Continuous.TreeVolume
import SortingAdversary.Continuous.TreeRouting
import SortingAdversary.Continuous.Normalization

/-!
# Elementary invariants of the concrete tree mutations

Normalization preserves fresh isolated unit coordinates. All mutations keep
the stored bounds inside the unit interval, and recording a comparison can
affect an untouched coordinate only when that coordinate is queried.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion

variable {n : ℕ}

def State.UnitBounds (s : State n ℝ) : Prop :=
  ∀ x, 0 ≤ s.system.lower x ∧ s.system.upper x ≤ 1

theorem initial_unitBounds : (initial n : State n ℝ).UnitBounds := by
  intro x
  simp [initial]

theorem initial_isolatedUnit (x : Fin n) : IsolatedUnit (initial n : State n ℝ).system x := by
  simp [IsolatedUnit, initial]

theorem refineAt_unitBounds (s : State n ℝ) (hs : s.UnitBounds)
    (x : Fin n) (c : ℝ) : (refineAt s x c).UnitBounds := by
  intro y
  by_cases hy : y = x
  · subst y
    simp [refineAt, resetCoordinate]
  · constructor
    · simp only [refineAt, resetCoordinate, if_neg hy]
      split_ifs
      · exact (hs y).1.trans (le_max_left _ _)
      · exact (hs y).1
    · simp only [refineAt, resetCoordinate, if_neg hy]
      split_ifs
      · exact (min_le_left _ _).trans (hs y).2
      · exact (hs y).2

theorem normalize_unitBounds (s : State n ℝ) (hs : s.UnitBounds)
    (order : List (Fin n)) : (normalize s order).UnitBounds := by
  intro x
  constructor
  · change 0 ≤ (OrderRegion.normalize s.system order).lower x
    simp only [OrderRegion.normalize, OrderRegion.upperPass_lower]
    exact (hs x).1.trans (OrderRegion.lowerPass_increases s.system order x)
  · change (OrderRegion.normalize s.system order).upper x ≤ 1
    apply (OrderRegion.upperPass_decreases _ order.reverse x).trans
    simpa only [OrderRegion.lowerPass_upper] using (hs x).2

theorem normalize_localArcs (s : State n ℝ) (hs : s.LocalArcs)
    (order : List (Fin n)) : (normalize s order).LocalArcs := by
  intro x y hxy
  exact hs x y (by simpa [normalize, OrderRegion.normalize_edge] using hxy)

theorem propagateLower_isolatedUnit (D : System (Fin n) ℝ) (x v : Fin n)
    (h : IsolatedUnit D x) : IsolatedUnit (propagateLower D v) x := by
  refine ⟨?_, h.2.1, h.2.2⟩
  by_cases hx : x = v
  · subst v
    simp only [propagateLower, Function.update_self]
    have hempty : (Finset.univ.filter fun y => D.edge y x) = ∅ := by
      ext y
      simp [(h.2.2 y).2]
    simp [conditionalLower, hempty, h.1]
  · simpa [propagateLower, hx] using h.1

theorem propagateUpper_isolatedUnit (D : System (Fin n) ℝ) (x v : Fin n)
    (h : IsolatedUnit D x) : IsolatedUnit (propagateUpper D v) x := by
  refine ⟨h.1, ?_, h.2.2⟩
  by_cases hx : x = v
  · subst v
    simp only [propagateUpper, Function.update_self]
    have hempty : (Finset.univ.filter fun y => D.edge x y) = ∅ := by
      ext y
      simp [(h.2.2 y).1]
    simp [conditionalUpper, hempty, h.2.1]
  · simpa [propagateUpper, hx] using h.2.1

theorem normalize_isolatedUnit (D : System (Fin n) ℝ) (x : Fin n)
    (h : IsolatedUnit D x) (order : List (Fin n)) :
    IsolatedUnit (OrderRegion.normalize D order) x := by
  have hlo : ∀ (xs : List (Fin n)) (D : System (Fin n) ℝ), IsolatedUnit D x →
      IsolatedUnit (xs.foldl propagateLower D) x := by
    intro xs
    induction xs with
    | nil => intro D h; exact h
    | cons v xs ih =>
      intro D h
      exact ih (propagateLower D v) (propagateLower_isolatedUnit D x v h)
  have hhi : ∀ (xs : List (Fin n)) (D : System (Fin n) ℝ), IsolatedUnit D x →
      IsolatedUnit (xs.foldl propagateUpper D) x := by
    intro xs
    induction xs with
    | nil => intro D h; exact h
    | cons v xs ih =>
      intro D h
      exact ih (propagateUpper D v) (propagateUpper_isolatedUnit D x v h)
  exact hhi order.reverse _ (hlo order D h)

theorem record_unitBounds (s : State n ℝ) (hs : s.UnitBounds)
    (q : Query n) (a : Answer) : (record s q a).UnitBounds := by
  intro x
  cases hr : route (s.location q.left) (s.location q.right) <;> cases a <;>
    simp only [record, recordSystem, hr]
  all_goals
    have hlo := (hs x).1
    have hhi := (hs x).2
    by_cases hl : x = q.left <;> by_cases hr : x = q.right <;>
      simp_all [addArc, boundBelow, boundAbove, le_max_iff, min_le_iff]

theorem record_preserves_isolatedUnit (s : State n ℝ) (q : Query n) (a : Answer)
    (x : Fin n) (hx : x ≠ q.left) (hy : x ≠ q.right)
    (h : IsolatedUnit s.system x) : IsolatedUnit (record s q a).system x := by
  cases hr : route (s.location q.left) (s.location q.right) <;> cases a <;>
    simp only [record, recordSystem, hr]
  all_goals
    first
    | exact h
    | refine ⟨?_, ?_, ?_⟩
      · simpa [addArc, boundAbove, boundBelow, hx, hy] using h.1
      · simpa [addArc, boundAbove, boundBelow, hx, hy] using h.2.1
      · intro y
        simp [addArc, boundAbove, boundBelow, hx, hy, (h.2.2 y).1, (h.2.2 y).2]

end SortingAdversary.Continuous.TreeState
