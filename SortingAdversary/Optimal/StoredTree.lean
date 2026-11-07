import SortingAdversary.Optimal.TreePromotion
import SortingAdversary.Optimal.NumericalRepresentation
import SortingAdversary.Optimal.PaletteBirthOrder
import SortingAdversary.Optimal.Materialize

/-!
# Runtime storage for the recursive tree

Each concrete node stores its sparse source/active rows and chronological
palette permutation alongside its pool. Erasure exposes exactly the pool tree
used by the accounting proofs. All data are retained by actual transitions;
no source history is reconstructed by choice from a semantic equality.
-/

namespace SortingAdversary.Optimal

open PoolState WeakMaps WeakMaps.WeakSystem NumericalRepresentation
open FiniteRefinement FreshAdmission

variable {n : ℕ}

structure LocalData (p : Pool n) where
  rows : SourcePartition p.system p.pins
  order : Equiv.Perm (Fin (p.palette + 1))

/-- Materialize the primitive sparse metadata as well as both directions of
the chronological palette permutation. This resets lookup depth after each
physical answer while preserving every source-row identity. -/
def LocalData.materialize {p : Pool n} (d : LocalData p) : LocalData p where
  rows := {
    source := SparseClosure.lookup (SparseClosure.tabulate d.rows.source)
    active := SparseClosure.lookup (SparseClosure.tabulate d.rows.active)
    proper := by simpa only [SparseClosure.lookup_tabulate] using d.rows.proper
    public_eq := by simpa only [SparseClosure.lookup_tabulate] using d.rows.public_eq
    active_source := by simpa only [SparseClosure.lookup_tabulate] using d.rows.active_source
    active_free := by simpa only [SparseClosure.lookup_tabulate] using d.rows.active_free
    covered := by simpa only [SparseClosure.lookup_tabulate] using d.rows.covered }
  order := Materialize.permutation d.order

@[simp] theorem LocalData.materialize_eq {p : Pool n} (d : LocalData p) :
    d.materialize = d := by
  cases d with
  | mk rows order =>
    cases rows
    simp only [LocalData.materialize, SparseClosure.lookup_tabulate, Materialize.permutation_eq]

theorem false_closure (n : ℕ) :
    SparseClosure.closure (fun _ _ : Fin n => false) = fun x y => decide (x = y) := by
  funext x y
  apply Bool.eq_iff_iff.mpr
  constructor
  · apply closure_subset_closed (fun _ _ => false) (fun x y : Fin n => decide (x = y))
      (by intro x; simp)
      (by intro x y z hxy hyz; simpa using (of_decide_eq_true hxy).trans (of_decide_eq_true hyz))
      (by intro x y h; contradiction) x y
  · intro h
    have he : x = y := of_decide_eq_true h
    subst y
    exact SparseClosure.closure_refl _ _

def emptyData (n : ℕ) : LocalData (emptyPool n) where
  rows := {
    source := fun _ _ => false
    active := fun _ _ => false
    proper := by intro u v h; contradiction
    public_eq := (false_closure n).symm
    active_source := by intro u v h; contradiction
    active_free := by intro u v h; contradiction
    covered := by intro u v h; contradiction }
  order := Equiv.refl _

def initialData (N : ℕ) : LocalData (initialRoot N) where
  rows := {
    source := fun _ _ => false
    active := fun _ _ => false
    proper := by intro u v h; contradiction
    public_eq := (false_closure (N + 2)).symm
    active_source := by intro u v h; contradiction
    active_free := by intro u v h; contradiction
    covered := by intro u v h; contradiction }
  order := Equiv.refl _

def LocalData.admission (p : Pool n) (d : LocalData p) (v : Fin n) (hv : v ∉ p.members) :
    LocalData (p.admission v hv).next := by
  unfold Pool.admission
  split
  · exact ⟨d.rows.admit v (p.system.lower v) (p.outside v hv).2, d.order⟩
  · exact ⟨d.rows.append.admit v (p.append.system.lower v)
      (p.append.outside v (by simpa using hv)).2, PaletteBirthOrder.extendTop d.order⟩

inductive StoredTree (n : ℕ) where
  | node (identity : ℕ) (pool : Pool n) (data : LocalData pool)
      (children : List (ℕ × StoredTree n))

namespace StoredTree

def pool : StoredTree n → Pool n
  | .node _ p _ _ => p

def data : (t : StoredTree n) → LocalData t.pool
  | .node _ _ d _ => d

def erase : StoredTree n → PoolTree.Tree n
  | .node identity p _ children =>
    .node identity p (children.map (fun a => (a.1, erase a.2)))
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

@[simp] theorem erase_pool (t : StoredTree n) : t.erase.pool = t.pool := by
  cases t with | node identity p d children => rw [erase]; rfl

def erasedChildren (children : List (ℕ × StoredTree n)) : List (ℕ × PoolTree.Tree n) :=
  children.map (fun a => (a.1, a.2.erase))

def empty (n identity : ℕ) : StoredTree n := .node identity (emptyPool n) (emptyData n) []
def initial (N : ℕ) : StoredTree (N + 2) := .node 0 (initialRoot N) (initialData N) []

@[simp] theorem erase_empty (n identity : ℕ) : (empty n identity).erase = PoolTree.Tree.empty n identity := by
  rw [empty, erase]
  rfl
@[simp] theorem erase_initial (N : ℕ) : (initial N).erase = PoolTree.Tree.initial N := by
  rw [initial, erase]
  rfl

def mapKeys {K L : ℕ} (e : Fin K → Fin L) (children : List (ℕ × StoredTree n)) :
    List (ℕ × StoredTree n) := children.map (fun a => (ColourTransport.extend e a.1, a.2))

theorem erased_mapKeys {K L : ℕ} (e : Fin K → Fin L) (children : List (ℕ × StoredTree n)) :
    erasedChildren (mapKeys e children) = PoolTree.Tree.mapKeys e (erasedChildren children) := by
  simp [erasedChildren, mapKeys, PoolTree.Tree.mapKeys, Function.comp_def]

def admitRoot (t : StoredTree n) (v : Fin n) (hv : v ∉ t.pool.members) : StoredTree n :=
  match t with
  | .node identity p d children =>
    let a := p.admission v hv
    .node identity a.next (d.admission p v hv) (mapKeys a.embed children)

theorem semantic_admit_congr {t u : PoolTree.Tree n} (he : t = u) (v : Fin n)
    (ht : v ∉ t.pool.members) (hu : v ∉ u.pool.members) :
    t.admitRoot v ht = u.admitRoot v hu := by
  cases he
  rfl

theorem erase_admitRoot (t : StoredTree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    (t.admitRoot v hv).erase = t.erase.admitRoot v (by simpa using hv) := by
  cases t with
  | node identity p d children =>
    have he : (StoredTree.node identity p d children).erase =
        PoolTree.Tree.node identity p (erasedChildren children) := by rw [erase]; rfl
    rw [semantic_admit_congr he v _ (by exact hv)]
    rw [admitRoot, erase]
    exact congrArg (PoolTree.Tree.node identity (p.admission v hv).next)
      (erased_mapKeys (p.admission v hv).embed children)

@[simp] theorem admitRoot_members (t : StoredTree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    (t.admitRoot v hv).pool.members = insert v t.pool.members := by
  cases t with | node identity p d children => exact (p.admission v hv).members_eq

def freshChild (n identity : ℕ) (v : Fin n) : StoredTree n :=
  (empty n identity).admitRoot v (by simp [empty, pool, emptyPool])

@[simp] theorem erase_freshChild (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).erase = PoolTree.Tree.freshChild n identity v := by
  simp only [freshChild, erase_admitRoot, erase_empty, PoolTree.Tree.freshChild]

/-- Public rows, primitive endpoints, pins, sparse metadata, and palette
permutations are cached after a physical answer. Source identities are exact. -/
def materialize : StoredTree n → StoredTree n
  | .node identity p d children =>
    .node identity (Materialize.pool p)
      (by rw [Materialize.pool_eq]; exact d.materialize)
      (children.map (fun a => (a.1, materialize a.2)))
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

@[simp] theorem erase_materialize (t : StoredTree n) : t.materialize.erase = t.erase := by
  cases t with
  | node identity p d children =>
    rw [materialize, erase, erase, Materialize.pool_eq]
    congr 1
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro a ha
    rw [erase_materialize a.2]
termination_by sizeOf t
decreasing_by
  have h := List.sizeOf_lt_of_mem ha
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

end StoredTree
end SortingAdversary.Optimal
