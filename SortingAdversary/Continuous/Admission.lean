import SortingAdversary.Continuous.Counting

/-!
# Insertion inside an existing child block

The continuous refinement proof restores a moved item at the parent's anchor,
then perturbs it just before and just after the existing child block. Both
orders satisfy the transcript. This file proves the combinatorial conclusion
using actual rankings and actual comparison histories: every intermediate
insertion satisfies that same history.

This is the insertion part of the admission argument. Its use for the concrete
tree still requires the geometric construction of the two endpoint orders.
-/

namespace SortingAdversary.Continuous

/-- Every pairwise comparison common to the two extreme insertions is true
at every intermediate insertion. Existing labels retain their relative order. -/
theorem insertRanking_order_between {n : ℕ} (π : Ranking n)
    (r₀ r r₁ : Fin (n + 1)) (hr₀ : r₀ ≤ r) (hr₁ : r ≤ r₁)
    (x y : Fin (n + 1))
    (h₀ : insertRanking r₀ π x < insertRanking r₀ π y)
    (h₁ : insertRanking r₁ π x < insertRanking r₁ π y) :
    insertRanking r π x < insertRanking r π y := by
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y, rfl⟩
    · exact (lt_irrefl _ h₀).elim
    · simp only [insertRanking_zero, insertRanking_succ,
        Fin.lt_succAbove_iff_le_castSucc] at h₁ ⊢
      exact hr₁.trans h₁
  · rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y, rfl⟩
    · simp only [insertRanking_zero, insertRanking_succ,
        Fin.succAbove_lt_iff_castSucc_lt] at h₀ ⊢
      exact h₀.trans_le hr₀
    · simpa only [insertRanking_succ, Fin.succAbove_lt_succAbove_iff] using h₀

theorem insertRanking_observation_between {n : ℕ} (π : Ranking n)
    (r₀ r r₁ : Fin (n + 1)) (hr₀ : r₀ ≤ r) (hr₁ : r ≤ r₁)
    (o : Observation (n + 1))
    (h₀ : o.Holds (insertRanking r₀ π)) (h₁ : o.Holds (insertRanking r₁ π)) :
    o.Holds (insertRanking r π) := by
  cases o with
  | mk q a =>
    cases a with
    | less => exact insertRanking_order_between π r₀ r r₁ hr₀ hr₁ q.left q.right h₀ h₁
    | greater => exact insertRanking_order_between π r₀ r r₁ hr₀ hr₁ q.right q.left h₀ h₁

/-- Pairwise transcript constraints cannot forbid an intermediate insertion
while admitting both extreme positions. This includes comparisons between the
new label and old labels, not just transcripts omitting the new label. -/
theorem compatible_insertRanking_between {n : ℕ} (π : Ranking n)
    (r₀ r r₁ : Fin (n + 1)) (hr₀ : r₀ ≤ r) (hr₁ : r ≤ r₁)
    (h : History (n + 1))
    (h₀ : Compatible (insertRanking r₀ π) h)
    (h₁ : Compatible (insertRanking r₁ π) h) :
    Compatible (insertRanking r π) h := by
  induction h with
  | nil => exact compatible_nil _
  | cons o h ih =>
    rw [compatible_cons] at h₀ h₁ ⊢
    exact ⟨insertRanking_observation_between π r₀ r r₁ hr₀ hr₁ o h₀.1 h₁.1,
      ih h₀.2 h₁.2⟩

end SortingAdversary.Continuous
