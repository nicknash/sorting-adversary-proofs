import SortingAdversary.Optimal.PrimitiveWork
import SortingAdversary.Optimal.SparseClosure

/-!
# Primitive work of materialized transitive closure

The counted code evaluates every source-row callback once when constructing
the initial matrix. Every Floyd step then reads only stored Boolean entries.
The counter includes both array levels, Boolean operations, list inspection,
and the construction of the finite pivot list. In particular, a nested
functional expression for the input relation is not assumed to be a unit-cost
lookup.
-/

namespace SortingAdversary.Optimal.ClosureWork

open PrimitiveWork SparseClosure

variable {n : ℕ}

abbrev Rows (n : ℕ) := Fin n → Fin n → PrimitiveWork.Result Bool

def values (rows : Rows n) : SparseClosure.Rows (Fin n) :=
  fun x y => (rows x y).value

def tabulate (rows : Rows n) : PrimitiveWork.Result (Table n) :=
  PrimitiveWork.vector (fun x => PrimitiveWork.vector (rows x))

@[simp] theorem tabulate_value (rows : Rows n) :
    (tabulate rows).value = SparseClosure.tabulate (values rows) := by
  simp only [tabulate, PrimitiveWork.vector_value, SparseClosure.tabulate, values]

theorem tabulate_work_le (rows : Rows n) (bound : ℕ)
    (h : ∀ x y, (rows x y).work ≤ bound) :
    (tabulate rows).work ≤ n * (n * (bound + 2) + 2) := by
  apply PrimitiveWork.vector_work_le
  intro x
  exact PrimitiveWork.vector_work_le _ bound (h x)

/-- Six indexed reads and two Boolean operations. All three matrix entries
are evaluated before the Boolean expression, so the bound is independent of
short-circuit implementation choices. -/
def via (T : Table n) (k : Fin n) : PrimitiveWork.Result (Table n) :=
  tabulate (fun x y => ⟨T[x][y] || (T[x][k] && T[k][y]), 8⟩)

@[simp] theorem via_value (T : Table n) (k : Fin n) :
    (via T k).value = tableVia T k := by
  simp only [via, tabulate_value]
  rfl

theorem via_work_le (T : Table n) (k : Fin n) :
    (via T k).work ≤ n * (n * 10 + 2) :=
  tabulate_work_le _ 8 (fun _ _ => le_rfl)

def along (T : Table n) : List (Fin n) → PrimitiveWork.Result (Table n)
  | [] => ⟨T, 1⟩
  | k :: ks =>
      let step := via T k
      let rest := along step.value ks
      ⟨rest.value, step.work + rest.work + 1⟩

@[simp] theorem along_value (T : Table n) (ks : List (Fin n)) :
    (along T ks).value = tableAlong T ks := by
  induction ks generalizing T with
  | nil => rfl
  | cons k ks ih => simp only [along, ih, via_value, tableAlong]

theorem along_work_le (T : Table n) (ks : List (Fin n)) :
    (along T ks).work ≤ ks.length * (n * (n * 10 + 2) + 1) + 1 := by
  induction ks generalizing T with
  | nil => simp [along]
  | cons k ks ih =>
    have hs := via_work_le T k
    have ht := ih (via T k).value
    simp only [along, List.length_cons, Nat.add_mul, one_mul]
    omega

def reflexiveRows (rows : Rows n) : Rows n := fun x y =>
  let old := rows x y
  ⟨old.value || decide (x = y), old.work + 2⟩

@[simp] theorem reflexiveRows_value (rows : Rows n) :
    values (reflexiveRows rows) = reflexive (values rows) := by
  funext x y
  simp only [values, reflexiveRows, reflexive]

/-- Finite index-list generation uses at most three word operations per
element (successor, constructor, and loop test). -/
def closure (rows : Rows n) : PrimitiveWork.Result (Table n) :=
  let initial := tabulate (reflexiveRows rows)
  let finished := along initial.value (List.finRange n)
  ⟨finished.value, initial.work + finished.work + 3 * n + 1⟩

@[simp] theorem closure_value (rows : Rows n) :
    (closure rows).value = tableClosure (values rows) := by
  simp only [closure, along_value, tabulate_value, reflexiveRows_value, tableClosure]

def workBound (n rowWork : ℕ) : ℕ :=
  n * (n * (rowWork + 4) + 2) + n * (n * (n * 10 + 2) + 1) + 3 * n + 2

theorem closure_work_le (rows : Rows n) (bound : ℕ)
    (h : ∀ x y, (rows x y).work ≤ bound) :
    (closure rows).work ≤ workBound n bound := by
  have hi := tabulate_work_le (reflexiveRows rows) (bound + 2)
    (fun x y => Nat.add_le_add_right (h x y) 2)
  have hf := along_work_le (tabulate (reflexiveRows rows)).value (List.finRange n)
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at hi hf
  change (tabulate (reflexiveRows rows)).work +
    (along (tabulate (reflexiveRows rows)).value (List.finRange n)).work + 3 * n + 1 ≤ _
  unfold workBound
  omega

end SortingAdversary.Optimal.ClosureWork
