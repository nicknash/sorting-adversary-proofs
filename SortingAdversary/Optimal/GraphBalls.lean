import SortingAdversary.Optimal.WeakMaps
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sparse generating-graph balls

These are balls in the undirected graph of the actual raw rows. Reflexive rows
are ignored in the degree. The breadth expansion and its cardinal bounds are
finite and independent of any transitive closure used for logical queries.
-/

namespace SortingAdversary.Optimal.GraphBalls

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Proper undirected neighbors of a raw generating relation. -/
def neighbors (E : α → α → Bool) (v : α) : Finset α :=
  Finset.univ.filter (fun w => w ≠ v ∧ (E v w = true ∨ E w v = true))

/-- Include the current vertex, so breadth expansion uses walks of at most the
specified length. -/
def closedNeighbors (E : α → α → Bool) (v : α) : Finset α :=
  insert v (neighbors E v)

@[simp] theorem mem_neighbors (E : α → α → Bool) (v w : α) :
    w ∈ neighbors E v ↔ w ≠ v ∧ (E v w = true ∨ E w v = true) := by
  simp [neighbors]

@[simp] theorem mem_closedNeighbors (E : α → α → Bool) (v w : α) :
    w ∈ closedNeighbors E v ↔ w = v ∨ E v w = true ∨ E w v = true := by
  simp only [closedNeighbors, Finset.mem_insert, mem_neighbors]
  tauto

theorem closedNeighbors_symm (E : α → α → Bool) (v w : α) :
    w ∈ closedNeighbors E v ↔ v ∈ closedNeighbors E w := by
  simp only [mem_closedNeighbors]
  tauto

/-- A finite breadth-first ball of radius `r`, retaining all old vertices at
successive expansions. -/
def ball (E : α → α → Bool) (v : α) : ℕ → Finset α
  | 0 => {v}
  | r + 1 => (closedNeighbors E v).biUnion (fun w => ball E w r)

@[simp] theorem ball_zero (E : α → α → Bool) (v : α) : ball E v 0 = {v} := rfl

@[simp] theorem mem_ball_succ (E : α → α → Bool) (v w : α) (r : ℕ) :
    w ∈ ball E v (r + 1) ↔ ∃ u ∈ closedNeighbors E v, w ∈ ball E u r := by
  simp only [ball, Finset.mem_biUnion]

theorem ball_step (E : α → α → Bool) (v : α) (r : ℕ) :
    ball E v r ⊆ ball E v (r + 1) := by
  intro w hw
  exact (mem_ball_succ E v w r).mpr ⟨v, by simp, hw⟩

theorem ball_mono (E : α → α → Bool) (v : α) {r s : ℕ} (h : r ≤ s) :
    ball E v r ⊆ ball E v s := by
  induction s, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ s h ih => exact ih.trans (ball_step E v s)

theorem center_mem_ball (E : α → α → Bool) (v : α) (r : ℕ) : v ∈ ball E v r :=
  ball_mono E v (Nat.zero_le r) (by simp)

/-- Concatenating two bounded walks adds their radii. -/
theorem mem_ball_add (E : α → α → Bool) {v x y : α} {r s : ℕ}
    (hx : x ∈ ball E v r) (hy : y ∈ ball E x s) : y ∈ ball E v (r + s) := by
  induction r generalizing v with
  | zero =>
    have : x = v := Finset.mem_singleton.mp hx
    subst x
    simpa using hy
  | succ r ih =>
    obtain ⟨w, hw, hxw⟩ := (mem_ball_succ E v x r).mp hx
    have h := (mem_ball_succ E v y (r + s)).mpr ⟨w, hw, ih hxw⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem mem_ball_one (E : α → α → Bool) (v w : α) :
    w ∈ ball E v 1 ↔ w ∈ closedNeighbors E v := by
  simp only [mem_ball_succ, ball_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hw; exact ⟨w, hw, rfl⟩

theorem ball_symm (E : α → α → Bool) {v w : α} {r : ℕ}
    (h : w ∈ ball E v r) : v ∈ ball E w r := by
  induction r generalizing v w with
  | zero => simpa only [ball_zero, Finset.mem_singleton, eq_comm] using h
  | succ r ih =>
    obtain ⟨u, hu, hwu⟩ := (mem_ball_succ E v w r).mp h
    have huv : v ∈ ball E u 1 := (mem_ball_one E u v).mpr
      ((closedNeighbors_symm E v u).mp hu)
    exact mem_ball_add E (ih hwu) huv

theorem closedNeighbors_card_le (E : α → α → Bool) (d : ℕ)
    (hdegree : ∀ v, (neighbors E v).card ≤ d) (v : α) :
    (closedNeighbors E v).card ≤ d + 1 := by
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hdegree v) 1)

/-- A radius `r` ball has at most `(d+1)^r` vertices when the proper generating
neighbors have degree at most `d`. -/
theorem ball_card_le (E : α → α → Bool) (d : ℕ)
    (hdegree : ∀ v, (neighbors E v).card ≤ d) (v : α) (r : ℕ) :
    (ball E v r).card ≤ (d + 1) ^ r := by
  induction r generalizing v with
  | zero => simp
  | succ r ih =>
    calc
      _ ≤ ∑ w ∈ closedNeighbors E v, (ball E w r).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ closedNeighbors E v, (d + 1) ^ r := Finset.sum_le_sum (fun w _ => ih w)
      _ = (closedNeighbors E v).card * (d + 1) ^ r := by simp
      _ ≤ (d + 1) * (d + 1) ^ r := Nat.mul_le_mul_right _ (closedNeighbors_card_le E d hdegree v)
      _ = (d + 1) ^ (r + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Proper directed arcs used for the height witness. -/
def Arc (E : α → α → Bool) (x y : α) : Prop := x ≠ y ∧ E x y = true

/-- A rank witness bounds the length needed to reach every directed ancestor. -/
theorem ancestor_mem_ball_rank (E : α → α → Bool) (rank : α → ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y) {x v : α}
    (h : Relation.ReflTransGen (Arc E) x v) :
    rank x ≤ rank v ∧ x ∈ ball E v (rank v - rank x) := by
  induction h with
  | refl => exact ⟨le_rfl, by simp⟩
  | @tail v w hvw hstep ih =>
    have hrank := hstrict v w hstep
    refine ⟨ih.1.trans hrank.le, ?_⟩
    have hclose : v ∈ closedNeighbors E w := by
      simp only [mem_closedNeighbors]
      exact Or.inr (Or.inr hstep.2)
    have hball := (mem_ball_succ E w x (rank v - rank x)).mpr ⟨v, hclose, ih.2⟩
    exact ball_mono E w (by omega : rank v - rank x + 1 ≤ rank w - rank x) hball

/-- All ancestors of a vertex of rank below `H` lie within radius `H-1`. -/
theorem ancestor_mem_ball (E : α → α → Bool) (rank : α → ℕ) (H : ℕ)
    (hstrict : ∀ x y, Arc E x y → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) {x v : α}
    (h : Relation.ReflTransGen (Arc E) x v) : x ∈ ball E v (H - 1) := by
  have hr := ancestor_mem_ball_rank E rank hstrict h
  exact ball_mono E v (by have := hheight v; omega) hr.2

/-- Graph connectivity is used only to compare widths within one original
component. No widths or locations of unrelated components enter. -/
def Connected (E : α → α → Bool) (v w : α) : Prop := ∃ r, w ∈ ball E v r

theorem connected_of_mem_ball (E : α → α → Bool) {v w : α} {r : ℕ}
    (h : w ∈ ball E v r) : Connected E v w := ⟨r, h⟩

end SortingAdversary.Optimal.GraphBalls
