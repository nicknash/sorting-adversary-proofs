import SortingAdversary.Optimal.RepresentationRealize
import SortingAdversary.Optimal.RepresentationAdmission
import SortingAdversary.Optimal.RepresentationShape

/-!
# Stored recursive access to the actual tree

The representation contains one local getter record at every actual node
and an explicit linked list of its represented children. It does not obtain
child access through an uncharged higher-order lookup. Realization installs
the measured getters in the actual runtime fields and preserves the full
reference stored tree extensionally.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState

variable {n : ℕ}

mutual
  inductive TreeAccess : StoredTree n → Type where
    | node (identity : ℕ) (p : Pool n) (d : LocalData p)
        (access : LocalAccess (PassiveLocalState.state p d))
        {children : List (ℕ × StoredTree n)} (next : ChildrenAccess children) :
        TreeAccess (.node identity p d children)

  inductive ChildrenAccess : List (ℕ × StoredTree n) → Type where
    | nil : ChildrenAccess []
    | cons (key : ℕ) {t : StoredTree n} (child : TreeAccess t)
        {rest : List (ℕ × StoredTree n)} (next : ChildrenAccess rest) :
        ChildrenAccess ((key, t) :: rest)
end

mutual
  def TreeAccess.realize {t : StoredTree n} (a : TreeAccess t) : StoredTree n :=
    match a with
    | .node identity _ _ access children =>
      let s := access.realize
      .node identity s.pool ⟨s.rows, s.order⟩ children.realize

  def ChildrenAccess.realize {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts) :
      List (ℕ × StoredTree n) :=
    match a with
    | .nil => []
    | .cons key child rest => (key, child.realize) :: rest.realize
end

mutual
  @[simp] theorem TreeAccess.realize_eq {t : StoredTree n} (a : TreeAccess t) :
      a.realize = t := by
    cases a with
    | node identity p d access children =>
      simp only [TreeAccess.realize, ChildrenAccess.realize_eq]
      exact congrArg (fun s : State n => StoredTree.node identity s.pool
        (⟨s.rows, s.order⟩ : LocalData s.pool) _) (LocalAccess.realize_eq access)

  @[simp] theorem ChildrenAccess.realize_eq {ts : List (ℕ × StoredTree n)}
      (a : ChildrenAccess ts) : a.realize = ts := by
    cases a with
    | nil => rfl
    | cons key child rest =>
      simp only [ChildrenAccess.realize, TreeAccess.realize_eq, ChildrenAccess.realize_eq]
end

mutual
  def TreeAccess.Bound {t : StoredTree n} (a : TreeAccess t) (A : ℕ) : Prop :=
    match a with
    | .node _ _ _ access children => AccessBound access A ∧ children.Bound A

  def ChildrenAccess.Bound {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts) (A : ℕ) : Prop :=
    match a with
    | .nil => True
    | .cons _ child rest => child.Bound A ∧ rest.Bound A
end

namespace TreeAccess

/-- Read the actual state and child-list pointers already stored in the
node. This does not evaluate a semantic target transition. -/
def stored {t : StoredTree n} (a : TreeAccess t) : StoredTree n := by
  cases a with
  | @node identity p d _ children _ => exact .node identity p d children

@[simp] theorem stored_eq {t : StoredTree n} (a : TreeAccess t) : a.stored = t := by
  cases a
  rfl

def transport {t u : StoredTree n} (he : t = u) (a : TreeAccess t) : TreeAccess u := he ▸ a

theorem transport_bound {t u : StoredTree n} (he : t = u) (a : TreeAccess t)
    {A : ℕ} (h : a.Bound A) : (a.transport he).Bound A := by cases he; exact h

def rebased {t : StoredTree n} (a : TreeAccess t) : TreeAccess a.stored := a.transport a.stored_eq.symm

theorem rebased_bound {t : StoredTree n} (a : TreeAccess t) {A : ℕ} (h : a.Bound A) :
    a.rebased.Bound A := a.transport_bound _ h

def root {t : StoredTree n} (a : TreeAccess t) :
    LocalAccess (PassiveLocalState.state t.pool t.data) :=
  match a with
  | .node _ _ _ access _ => access

theorem root_bound {t : StoredTree n} (a : TreeAccess t) {A : ℕ} (h : a.Bound A) :
    AccessBound a.root A := by cases a; exact h.1

def initial (N : ℕ) : TreeAccess (StoredTree.initial N) :=
  .node 0 (initialRoot N) (initialData N) (RepresentationWork.initial N) .nil

theorem initial_bound (N : ℕ) : (initial N).Bound 2 := by
  refine ⟨?_, trivial⟩
  constructor <;> intros <;> norm_num only [initial, RepresentationWork.initial]

def empty (n identity : ℕ) : TreeAccess (StoredTree.empty n identity) :=
  .node identity (emptyPool n) (emptyData n) (emptyAccess n) .nil

theorem empty_bound (n identity : ℕ) : (empty n identity).Bound 2 := by
  refine ⟨?_, trivial⟩
  constructor <;> intros <;> norm_num only [empty, emptyAccess]

end TreeAccess

namespace ChildrenAccess

/-- The spine after its first cell is already present in the representation;
reading it is a fixed number of pointer accesses. -/
def stored {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts) : List (ℕ × StoredTree n) := by
  cases a with
  | nil => exact []
  | @cons key tree _ rest _ => exact (key, tree) :: rest

@[simp] theorem stored_eq {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts) : a.stored = ts := by
  cases a <;> rfl

def transport {ts us : List (ℕ × StoredTree n)} (he : ts = us) (a : ChildrenAccess ts) :
    ChildrenAccess us := he ▸ a

theorem transport_bound {ts us : List (ℕ × StoredTree n)} (he : ts = us)
    (a : ChildrenAccess ts) {A : ℕ} (h : a.Bound A) : (a.transport he).Bound A := by
  cases he
  exact h

def rebased {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts) : ChildrenAccess a.stored :=
  a.transport a.stored_eq.symm

theorem rebased_bound {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    {A : ℕ} (h : a.Bound A) : a.rebased.Bound A := a.transport_bound _ h

def append {ts us : List (ℕ × StoredTree n)} (a : ChildrenAccess ts) (b : ChildrenAccess us) :
    Result (ChildrenAccess (ts ++ us)) :=
  match a with
  | .nil => ⟨b, 1⟩
  | .cons key child rest =>
    let tail := rest.append b
      let next := ChildrenAccess.cons key child.rebased tail.value.rebased
      have eq : (key, child.stored) :: tail.value.stored = _ := by
        rw [child.stored_eq, tail.value.stored_eq]
        rfl
      ⟨next.transport eq, tail.work + 12⟩

theorem append_bound {ts us : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (b : ChildrenAccess us) {A : ℕ} (ha : a.Bound A) (hb : b.Bound A) :
    (a.append b).value.Bound A := by
  cases a with
  | nil => exact hb
  | cons key child rest =>
    apply transport_bound
    exact ⟨child.rebased_bound ha.1, rebased_bound _ (append_bound rest b ha.2 hb)⟩

theorem append_work {ts us : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (b : ChildrenAccess us) : (a.append b).work = 12 * ts.length + 1 := by
  cases a with
  | nil => rfl
  | cons key child rest =>
    simp only [append, append_work rest b, List.length_cons]
    omega

end ChildrenAccess

namespace TreeAccess

/-- Store the computed local representation and the computed child-list
pointers. The reference state and child list occur only in equality proofs. -/
def pack (identity : ℕ) {s : State n} (access : LocalAccess s)
    (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members)
    {ts : List (ℕ × StoredTree n)} (children : ChildrenAccess ts) :
    Result (TreeAccess (.node identity s.pool ⟨s.rows, s.order⟩ ts)) :=
  let current := access.realizeWith palette members hp hm
  let currentAccess := access.rebasedWith palette members hp hm
  let represented := TreeAccess.node identity current.pool ⟨current.rows, current.order⟩
    currentAccess children.rebased
  have eq : StoredTree.node identity current.pool ⟨current.rows, current.order⟩ children.stored =
      .node identity s.pool ⟨s.rows, s.order⟩ ts := by
    rw [children.stored_eq]
    exact congrArg (fun u : State n => StoredTree.node identity u.pool ⟨u.rows, u.order⟩ ts)
      (access.realizeWith_eq palette members hp hm)
  ⟨represented.transport eq, 40⟩

theorem pack_bound (identity : ℕ) {s : State n} (access : LocalAccess s)
    (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members)
    {ts : List (ℕ × StoredTree n)} (children : ChildrenAccess ts)
    {A : ℕ} (ha : AccessBound access A) (hc : children.Bound A) :
    (pack identity access palette members hp hm children).value.Bound A :=
  transport_bound _ _ ⟨access.rebasedWith_bound palette members hp hm ha, children.rebased_bound hc⟩

theorem pack_work (identity : ℕ) {s : State n} (access : LocalAccess s)
    (palette : ℕ) (members : Finset (Fin n))
    (hp : palette = s.pool.palette) (hm : members = s.pool.members)
    {ts : List (ℕ × StoredTree n)} (children : ChildrenAccess ts) :
    (pack identity access palette members hp hm children).work = 40 := rfl

end TreeAccess

end SortingAdversary.Optimal.RepresentationWork
