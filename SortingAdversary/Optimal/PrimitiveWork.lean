import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# A counted finite-loop model

One unit is a primitive word operation: a scalar comparison or arithmetic
operation, an indexed array read/write, or one list-cell inspection. Input
functions return their own measured work, so their evaluation is never
silently treated as a constant-time oracle. Instrumentation counters are
ghost measurements of the value computation and are not charged recursively.

The elementary loops below execute the same tests that produce their values.
Later modules instantiate their callbacks with concrete matrix, endpoint,
palette and counting computations.
-/

namespace SortingAdversary.Optimal.PrimitiveWork

open scoped BigOperators

structure Result (α : Type*) where
  value : α
  work : ℕ
  deriving Repr

def pure (value : α) : Result α := ⟨value, 0⟩
def atom (value : α) : Result α := ⟨value, 1⟩

def bind (first : Result α) (next : α → Result β) : Result β :=
  let second := next first.value
  ⟨second.value, first.work + second.work⟩

def map (f : α → Result β) : List α → Result (List β)
  | [] => ⟨[], 1⟩
  | x :: xs =>
      let head := f x
      let tail := map f xs
      ⟨head.value :: tail.value, head.work + tail.work + 2⟩

@[simp] theorem map_value (f : α → Result β) (xs : List α) :
    (map f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [map, List.map_cons, ih]

theorem map_work (f : α → Result β) (xs : List α) :
    (map f xs).work = (xs.map (fun x => (f x).work + 2)).sum + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [map, List.map_cons, List.sum_cons, ih]; omega

theorem map_work_le (f : α → Result β) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (map f xs).work ≤ xs.length * (bound + 2) + 1 := by
  induction xs with
  | nil => simp [map]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [map, List.length_cons, Nat.add_mul, one_mul]
    omega

def find (f : α → Result Bool) : List α → Result (Option α)
  | [] => ⟨none, 1⟩
  | x :: xs =>
      let test := f x
      if test.value then ⟨some x, test.work + 2⟩
      else
        let tail := find f xs
        ⟨tail.value, test.work + tail.work + 2⟩

@[simp] theorem find_value (f : α → Result Bool) (xs : List α) :
    (find f xs).value = xs.find? (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [find, List.find?_cons]
    split <;> simp_all

theorem find_work_le (f : α → Result Bool) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (find f xs).work ≤ xs.length * (bound + 2) + 1 := by
  induction xs with
  | nil => simp [find]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [find, List.length_cons, Nat.add_mul, one_mul]
    split <;> dsimp only <;> omega

def any (f : α → Result Bool) (xs : List α) : Result Bool :=
  let found := find f xs
  ⟨found.value.isSome, found.work + 1⟩

@[simp] theorem any_value (f : α → Result Bool) (xs : List α) :
    (any f xs).value = xs.any (fun x => (f x).value) := by
  simp only [any, find_value, List.isSome_find?]

theorem any_work_le (f : α → Result Bool) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (any f xs).work ≤ xs.length * (bound + 2) + 2 := by
  have := find_work_le f xs bound h
  change (find f xs).work + 1 ≤ _
  omega

def all (f : α → Result Bool) (xs : List α) : Result Bool :=
  let opposite := any (fun x => let r := f x; ⟨!r.value, r.work + 1⟩) xs
  ⟨!opposite.value, opposite.work + 1⟩

@[simp] theorem all_value (f : α → Result Bool) (xs : List α) :
    (all f xs).value = xs.all (fun x => (f x).value) := by
  simp only [all, any_value]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, List.all_cons, Bool.not_or, Bool.not_not]
    rw [ih]

theorem all_work_le (f : α → Result Bool) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (all f xs).work ≤ xs.length * (bound + 3) + 3 := by
  have hb : ∀ x ∈ xs, (let r := f x; (⟨!r.value, r.work + 1⟩ : Result Bool)).work ≤ bound + 1 := by
    intro x hx
    dsimp only
    exact Nat.add_le_add_right (h x hx) 1
  have := any_work_le (fun x => let r := f x; ⟨!r.value, r.work + 1⟩) xs (bound + 1) hb
  change (any _ xs).work + 1 ≤ _
  simp only [Nat.add_assoc, Nat.reduceAdd] at this
  dsimp only at this ⊢
  omega

def count (f : α → Result Bool) : List α → Result ℕ
  | [] => ⟨0, 1⟩
  | x :: xs =>
      let test := f x
      let rest := count f xs
      ⟨(if test.value then 1 else 0) + rest.value, test.work + rest.work + 3⟩

@[simp] theorem count_value (f : α → Result Bool) (xs : List α) :
    (count f xs).value = (xs.filter (fun x => (f x).value)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [count, List.filter_cons]
    split <;> simp_all [Nat.add_comm]

theorem count_work_le (f : α → Result Bool) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (count f xs).work ≤ xs.length * (bound + 3) + 1 := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [count, List.length_cons, Nat.add_mul, one_mul]
    omega

/-- Every callback is evaluated once into a stored vector before its value
and counter are read. The two linear passes write values and read counters. -/
def vector (f : Fin n → Result α) : Result (Vector α n) :=
  let rows := Vector.ofFn f
  ⟨rows.map Result.value, (∑ x : Fin n, (rows[x]).work) + 2 * n⟩

@[simp] theorem vector_value (f : Fin n → Result α) :
    (vector f).value = Vector.ofFn (fun x => (f x).value) := by
  apply Vector.ext
  intro i hi
  simp [vector]

theorem vector_work (f : Fin n → Result α) :
    (vector f).work = (∑ x : Fin n, (f x).work) + 2 * n := by
  simp [vector, Fin.getElem_fin]

theorem vector_work_le (f : Fin n → Result α) (bound : ℕ) (h : ∀ x, (f x).work ≤ bound) :
    (vector f).work ≤ n * (bound + 2) := by
  rw [vector_work]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => h x)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at hs
  calc
    (∑ x, (f x).work) + 2 * n ≤ n * bound + 2 * n := Nat.add_le_add_right hs _
    _ = n * (bound + 2) := by simp [Nat.mul_add, Nat.mul_comm]

end SortingAdversary.Optimal.PrimitiveWork
