import SortingAdversary.Optimal.PoolTree
import SortingAdversary.Optimal.SparseClosure

/-!
# Materialized public rows, primitive walls, and physical pins

The functional semantic records are converted to stored vectors between
physical queries. This prevents repeated single-row closure expressions from
recursively recomputing old entries. The conversion is extensionally the
identity, so it changes neither the public order nor any numerical law.
-/

namespace SortingAdversary.Optimal.Materialize

open PoolState PoolTree WeakMaps SparseClosure
variable {n K : ℕ}

def system (S : WeakSystem (Fin n) K) : WeakSystem (Fin n) K :=
  let rows := tabulate S.edge
  let lower := Vector.ofFn S.lower
  let upper := Vector.ofFn S.upper
  { edge := lookup rows, lower := fun x => lower[x], upper := fun x => upper[x] }

@[simp] theorem system_eq (S : WeakSystem (Fin n) K) : system S = S := by
  cases S
  simp [system]

def pins (f : Fin n → Option (Fin K)) : Fin n → Option (Fin K) :=
  let table := Vector.ofFn f
  fun x => table[x]

@[simp] theorem pins_eq (f : Fin n → Option (Fin K)) : pins f = f := by
  funext x
  simp [pins]

def pool (p : Pool n) : Pool n where
  palette := p.palette
  positive := p.positive
  members := p.members
  system := system p.system
  pins := pins p.pins
  invariant := by simpa only [system_eq, pins_eq] using p.invariant
  pin_bounds := by simpa only [system_eq, pins_eq] using p.pin_bounds
  capacity := p.capacity
  outside := by simpa only [system_eq, pins_eq] using p.outside

@[simp] theorem pool_eq (p : Pool n) : pool p = p := by
  cases p
  simp [pool]

def tree : Tree n → Tree n
  | .node identity p children => .node identity (pool p) (children.map (fun a => (a.1, tree a.2)))
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

@[simp] theorem tree_eq (t : Tree n) : tree t = t := by
  cases t with
  | node identity p children =>
    rw [tree, pool_eq]
    congr 1
    have he : children.map (fun a => (a.1, tree a.2)) = children.map id := by
      apply List.map_congr_left
      intro a ha
      rw [tree_eq a.2]
      rfl
    simpa using he
termination_by sizeOf t
decreasing_by
  have h := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

/-- One local cache writes exactly the row matrix and three label vectors.
The counter records those writes in the same order as the stored conversion. -/
def poolCounted (p : Pool n) : Pool n × ℕ := (pool p, n * n + 3 * n)

@[simp] theorem poolCounted_value (p : Pool n) : (poolCounted p).1 = p := pool_eq p

@[simp] theorem poolCounted_writes (p : Pool n) : (poolCounted p).2 = n * n + 3 * n := rfl

def treeCounted : Tree n → Tree n × ℕ
  | .node identity p children =>
    let cached := poolCounted p
    let subtrees := children.map (fun a => (a.1, treeCounted a.2))
    (.node identity cached.1 (subtrees.map (fun a => (a.1, a.2.1))),
      cached.2 + (subtrees.map (fun a => a.2.2)).sum)
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem treeCounted_writes (t : Tree n) : (treeCounted t).2 = t.nodes * (n * n + 3 * n) := by
  cases t with
  | node identity p children =>
    rw [treeCounted, Tree.nodes]
    simp only [poolCounted_writes, List.map_map, Function.comp_def]
    have hchildren : (children.map (fun a => (treeCounted a.2).2)).sum =
        (children.map (fun a => a.2.nodes)).sum * (n * n + 3 * n) := by
      calc
        _ = (children.map (fun a => a.2.nodes * (n * n + 3 * n))).sum := by
          congr 1
          apply List.map_congr_left
          intro a ha
          exact treeCounted_writes a.2
        _ = _ := by
          induction children with
          | nil => simp
          | cons a rest ih => simp only [List.map_cons, List.sum_cons, Nat.add_mul, ih]
    rw [hchildren]
    simp [Nat.add_mul]
termination_by sizeOf t
decreasing_by
  have h := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

end SortingAdversary.Optimal.Materialize
