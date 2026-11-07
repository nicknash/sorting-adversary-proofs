import SortingAdversary.Optimal.WidthRepair
import SortingAdversary.Optimal.ClosureWork
import SortingAdversary.Optimal.StoredTree

/-!
# Measured access to the actual local representation

Every functional field has a concrete getter with its own work counter and
an exact-value theorem. The cache evaluates these getters into stored arrays;
subsequent accesses read those arrays. In particular, a function supplied as
an input is never declared to have constant lookup work by assumption.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState

variable {n : ℕ}

structure LocalAccess (s : State n) where
  publicRow : Fin n → Fin n → Result Bool
  source : Fin n → Fin n → Result Bool
  active : Fin n → Fin n → Result Bool
  lower : Fin n → Result (Fin (s.pool.palette + 1))
  upper : Fin n → Result (Fin (s.pool.palette + 1))
  pin : Fin n → Result (Option (Fin (s.pool.palette + 1)))
  member : Fin n → Result Bool
  order : Fin (s.pool.palette + 1) → Result (Fin (s.pool.palette + 1))
  inverse : Fin (s.pool.palette + 1) → Result (Fin (s.pool.palette + 1))
  publicRow_value : ∀ x y, (publicRow x y).value = s.pool.system.edge x y
  source_value : ∀ x y, (source x y).value = s.rows.source x y
  active_value : ∀ x y, (active x y).value = s.rows.active x y
  lower_value : ∀ x, (lower x).value = s.pool.system.lower x
  upper_value : ∀ x, (upper x).value = s.pool.system.upper x
  pin_value : ∀ x, (pin x).value = s.pool.pins x
  member_value : ∀ x, (member x).value = decide (x ∈ s.pool.members)
  order_value : ∀ x, (order x).value = s.order x
  inverse_value : ∀ x, (inverse x).value = s.order.symm x

structure AccessBound {s : State n} (a : LocalAccess s) (bound : ℕ) : Prop where
  publicRow : ∀ x y, (a.publicRow x y).work ≤ bound
  source : ∀ x y, (a.source x y).work ≤ bound
  active : ∀ x y, (a.active x y).work ≤ bound
  lower : ∀ x, (a.lower x).work ≤ bound
  upper : ∀ x, (a.upper x).work ≤ bound
  pin : ∀ x, (a.pin x).work ≤ bound
  member : ∀ x, (a.member x).work ≤ bound
  order : ∀ x, (a.order x).work ≤ bound
  inverse : ∀ x, (a.inverse x).work ≤ bound

namespace LocalAccess

variable {s : State n}

@[simp] theorem public_values (a : LocalAccess s) :
    ClosureWork.values a.publicRow = s.pool.system.edge := by
  funext x y
  exact a.publicRow_value x y

@[simp] theorem source_values (a : LocalAccess s) :
    ClosureWork.values a.source = s.rows.source := by
  funext x y
  exact a.source_value x y

@[simp] theorem active_values (a : LocalAccess s) :
    ClosureWork.values a.active = s.rows.active := by
  funext x y
  exact a.active_value x y

/-- Three matrices, four label vectors, and both palette directions are
evaluated once. The returned functions only read the resulting arrays. -/
def cache (a : LocalAccess s) : Result (LocalAccess s) :=
  let publicRows := ClosureWork.tabulate a.publicRow
  let sources := ClosureWork.tabulate a.source
  let activeRows := ClosureWork.tabulate a.active
  let lowers := PrimitiveWork.vector a.lower
  let uppers := PrimitiveWork.vector a.upper
  let pins := PrimitiveWork.vector a.pin
  let members := PrimitiveWork.vector a.member
  let orders := PrimitiveWork.vector a.order
  let inverses := PrimitiveWork.vector a.inverse
  ⟨{
    publicRow := fun x y => ⟨publicRows.value[x][y], 2⟩
    source := fun x y => ⟨sources.value[x][y], 2⟩
    active := fun x y => ⟨activeRows.value[x][y], 2⟩
    lower := fun x => ⟨lowers.value[x], 1⟩
    upper := fun x => ⟨uppers.value[x], 1⟩
    pin := fun x => ⟨pins.value[x], 1⟩
    member := fun x => ⟨members.value[x], 1⟩
    order := fun x => ⟨orders.value[x], 1⟩
    inverse := fun x => ⟨inverses.value[x], 1⟩
    publicRow_value := by intro x y; simp [publicRows, ClosureWork.tabulate_value, SparseClosure.tabulate]
    source_value := by intro x y; simp [sources, ClosureWork.tabulate_value, SparseClosure.tabulate]
    active_value := by intro x y; simp [activeRows, ClosureWork.tabulate_value, SparseClosure.tabulate]
    lower_value := by intro x; simp [lowers, a.lower_value]
    upper_value := by intro x; simp [uppers, a.upper_value]
    pin_value := by intro x; simp [pins, a.pin_value]
    member_value := by intro x; simp [members, a.member_value]
    order_value := by intro x; simp [orders, a.order_value]
    inverse_value := by intro x; simp [inverses, a.inverse_value] },
    publicRows.work + sources.work + activeRows.work + lowers.work + uppers.work +
      pins.work + members.work + orders.work + inverses.work + 9⟩

theorem cache_access (a : LocalAccess s) : AccessBound a.cache.value 2 := by
  constructor <;> intros <;> norm_num only [cache]

def cacheBound (n palette bound : ℕ) : ℕ :=
  3 * (n * (n * (bound + 2) + 2)) + 4 * (n * (bound + 2)) +
    2 * ((palette + 1) * (bound + 2)) + 9

theorem cache_work_le (a : LocalAccess s) {bound : ℕ} (h : AccessBound a bound) :
    a.cache.work ≤ cacheBound n s.pool.palette bound := by
  have hp := ClosureWork.tabulate_work_le a.publicRow bound h.publicRow
  have hs := ClosureWork.tabulate_work_le a.source bound h.source
  have ha := ClosureWork.tabulate_work_le a.active bound h.active
  have hl := PrimitiveWork.vector_work_le a.lower bound h.lower
  have hu := PrimitiveWork.vector_work_le a.upper bound h.upper
  have hi := PrimitiveWork.vector_work_le a.pin bound h.pin
  have hm := PrimitiveWork.vector_work_le a.member bound h.member
  have ho := PrimitiveWork.vector_work_le a.order bound h.order
  have hv := PrimitiveWork.vector_work_le a.inverse bound h.inverse
  change _ + _ + _ + _ + _ + _ + _ + _ + _ + 9 ≤ _
  unfold cacheBound
  omega

end LocalAccess

/-- The root has constant walls, no source rows or physical pins, and the
identity palette permutation. No arbitrary functional input is used. -/
def initial (N : ℕ) : LocalAccess
    (⟨initialRoot N, (initialData N).rows, (initialData N).order⟩ : State (N + 2)) where
  publicRow x y := ⟨decide (x = y), 1⟩
  source _ _ := ⟨false, 0⟩
  active _ _ := ⟨false, 0⟩
  lower _ := ⟨0, 0⟩
  upper _ := ⟨Fin.last (N + 1), 0⟩
  pin _ := ⟨none, 0⟩
  member _ := ⟨true, 0⟩
  order x := ⟨x, 0⟩
  inverse x := ⟨x, 0⟩
  publicRow_value _ _ := rfl
  source_value _ _ := rfl
  active_value _ _ := rfl
  lower_value _ := rfl
  upper_value _ := rfl
  pin_value _ := rfl
  member_value x := by simp [initialRoot]
  order_value _ := rfl
  inverse_value _ := rfl

theorem initial_bound (N : ℕ) : AccessBound (initial N) 1 := by
  constructor <;> intros <;> norm_num only [initial]

end SortingAdversary.Optimal.RepresentationWork
