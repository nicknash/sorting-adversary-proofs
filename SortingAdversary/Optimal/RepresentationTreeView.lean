import SortingAdversary.Optimal.RepresentationTreeBounds

/-! # Reading the already stored runtime node -/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState
variable {n : ℕ}

def storedLocalState (t : StoredTree n) : State n :=
  PassiveLocalState.state t.pool t.data

def storedRootChildren (t : StoredTree n) : List (ℕ × StoredTree n) :=
  match t with
  | .node _ _ _ children => children

structure NodeView (t : StoredTree n) where
  identity : ℕ
  state : State n
  children : List (ℕ × StoredTree n)
  root : LocalAccess state
  next : ChildrenAccess children
  actual : StoredRepair.node identity state children = t

namespace TreeAccess

def view {t : StoredTree n} (a : TreeAccess t) : NodeView t := by
  cases a with
  | @node identity p d access children next =>
    exact ⟨identity, PassiveLocalState.state p d, children, access, next, rfl⟩

theorem view_bound {t : StoredTree n} (a : TreeAccess t) {A : ℕ} (ha : a.Bound A) :
    AccessBound a.view.root A ∧ a.view.next.Bound A := by
  cases a
  exact ha

theorem view_state {identity : ℕ} {s : State n} {children : List (ℕ × StoredTree n)}
    (a : TreeAccess (StoredRepair.node identity s children)) : a.view.state = s :=
  congrArg storedLocalState a.view.actual

theorem view_children {identity : ℕ} {s : State n} {children : List (ℕ × StoredTree n)}
    (a : TreeAccess (StoredRepair.node identity s children)) : a.view.children = children :=
  congrArg storedRootChildren a.view.actual

end TreeAccess

/-- Only executable replay projections are retained. The specification
state, children, and allocator value are erased equality indices. -/
structure ReplayOutput (s : State n) (children : List (ℕ × StoredTree n)) (counter : ℕ) where
  state : State n
  nextChildren : List (ℕ × StoredTree n)
  access : LocalAccess state
  nextAccess : ChildrenAccess nextChildren
  nextCounter : ℕ
  state_eq : state = s
  children_eq : nextChildren = children
  counter_eq : nextCounter = counter
  cached : AccessBound access 2
  children_cached : nextAccess.Bound 2

def ReplayOutput.ofTree {identity : ℕ} {s : State n} {children : List (ℕ × StoredTree n)}
    (a : TreeAccess (StoredRepair.node identity s children)) (ha : a.Bound 2)
    (counter : ℕ) : ReplayOutput s children counter where
  state := a.view.state
  nextChildren := a.view.children
  access := a.view.root
  nextAccess := a.view.next
  nextCounter := counter
  state_eq := a.view_state
  children_eq := a.view_children
  counter_eq := rfl
  cached := (a.view_bound ha).1
  children_cached := (a.view_bound ha).2

end SortingAdversary.Optimal.RepresentationWork
