import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Fin.Basic

/-!
# Basic comparison-sorting objects

A `Ranking n` maps each of the `n` labelled items to its rank.  Thus the usual
ambiguity between "a permutation of positions" and "a permutation of items" is
removed from the formal statement: throughout this project, `π i` is the rank
of item `i`.
-/

namespace SortingAdversary

/-- The labelled items being sorted. -/
abbrev Item (n : ℕ) := Fin n

/-- A hidden input: a bijection from items to ranks. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

/-- The two possible outcomes of a comparison of distinct items. -/
inductive Answer where
  | less
  | greater
  deriving DecidableEq, Repr

/-- A legal comparison query.  Comparing an item with itself is excluded. -/
structure Query (n : ℕ) where
  left : Item n
  right : Item n
  distinct : left ≠ right

/-- The outcome of a query on a concrete hidden ranking. -/
def Query.outcome (π : Ranking n) (q : Query n) : Answer :=
  if π q.left < π q.right then .less else .greater

/-- One answered comparison. -/
structure Observation (n : ℕ) where
  query : Query n
  answer : Answer

/-- Whether an answered comparison is true in a concrete hidden ranking. -/
def Observation.Holds (π : Ranking n) (o : Observation n) : Prop :=
  match o.answer with
  | .less => π o.query.left < π o.query.right
  | .greater => π o.query.right < π o.query.left

/-- A comparison transcript, stored in any order. -/
abbrev History (n : ℕ) := List (Observation n)

/-- A ranking is compatible with every answer in a transcript. -/
def Compatible (π : Ranking n) (h : History n) : Prop :=
  h.Forall (Observation.Holds π)

@[simp] theorem compatible_nil (π : Ranking n) : Compatible π [] := by
  simp [Compatible]

@[simp] theorem compatible_cons (π : Ranking n) (o : Observation n) (h : History n) :
    Compatible π (o :: h) ↔ o.Holds π ∧ Compatible π h := by
  simp [Compatible]

/-- A concrete ranking always satisfies the answer obtained by consulting it. -/
theorem outcome_holds (π : Ranking n) (q : Query n) :
    (Observation.mk q (q.outcome π)).Holds π := by
  by_cases hlt : π q.left < π q.right
  · simp [Query.outcome, Observation.Holds, hlt]
  · have hne : π q.left ≠ π q.right := by
      intro h
      apply q.distinct
      exact π.injective h
    have hgt : π q.right < π q.left := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hlt h).elim
      · exact h
    simp [Query.outcome, Observation.Holds, hlt, hgt]

end SortingAdversary
