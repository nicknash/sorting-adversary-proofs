import SortingAdversary.Optimal.RepresentationTree
import SortingAdversary.Optimal.RepresentationTrace

/-!
# Measured admission in the represented recursive tree

Child keys are transported by an explicit counted list traversal. The
admission branch is selected by a measured population count, and all local
functional fields are cached before the updated node is stored. Unchanged
subtrees are shared without traversing their internal nodes.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState

variable {n K L : ℕ}

/-- Total finite-palette transport, including out-of-range stored keys. -/
def extendKey (get : Fin K → Result (Fin L)) (key : ℕ) : Result ℕ :=
  if h : key < K then
    let next := get ⟨key, h⟩
    ⟨next.value.val, next.work + 3⟩
  else ⟨L + (key - K), 4⟩

theorem extendKey_value (get : Fin K → Result (Fin L)) (e : Fin K → Fin L)
    (he : ∀ c, (get c).value = e c) (key : ℕ) :
    (extendKey get key).value = ColourTransport.extend e key := by
  simp only [extendKey, ColourTransport.extend]
  split <;> simp_all only

theorem extendKey_work (get : Fin K → Result (Fin L)) {C : ℕ}
    (hc : ∀ c, (get c).work ≤ C) (key : ℕ) : (extendKey get key).work ≤ C + 4 := by
  unfold extendKey
  split
  · rename_i h
    have hh := hc ⟨key, h⟩
    dsimp only
    omega
  · dsimp only
    omega

namespace ChildrenAccess

def mapKeys {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (e : Fin K → Fin L) (get : ℕ → Result ℕ)
    (he : ∀ key, (get key).value = ColourTransport.extend e key) :
    Result (ChildrenAccess (StoredTree.mapKeys e ts)) :=
  match a with
  | .nil => ⟨.nil, 1⟩
  | .cons key child rest =>
    let newKey := get key
    let tail := rest.mapKeys e get he
    let next := ChildrenAccess.cons newKey.value child.rebased tail.value.rebased
    have eq : (newKey.value, child.stored) :: tail.value.stored =
        StoredTree.mapKeys e ((key, _) :: _) := by
      rw [child.stored_eq, tail.value.stored_eq]
      simp only [StoredTree.mapKeys, List.map_cons, newKey, he]
    ⟨next.transport eq, newKey.work + tail.work + 12⟩

theorem mapKeys_bound {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (e : Fin K → Fin L) (get : ℕ → Result ℕ)
    (he : ∀ key, (get key).value = ColourTransport.extend e key)
    {A : ℕ} (ha : a.Bound A) : (a.mapKeys e get he).value.Bound A := by
  cases a with
  | nil => trivial
  | cons key child rest =>
    apply transport_bound
    exact ⟨child.rebased_bound ha.1, rebased_bound _ (mapKeys_bound rest e get he ha.2)⟩

theorem mapKeys_work {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (e : Fin K → Fin L) (get : ℕ → Result ℕ)
    (he : ∀ key, (get key).value = ColourTransport.extend e key)
    {C : ℕ} (hc : ∀ key, (get key).work ≤ C) :
    (a.mapKeys e get he).work ≤ ts.length * (C + 12) + 1 := by
  cases a with
  | nil => simp only [mapKeys, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons key child rest =>
    have ht := mapKeys_work rest e get he hc
    have hh := hc key
    simp only [mapKeys, List.length_cons, Nat.add_mul, one_mul]
    omega

end ChildrenAccess

namespace LocalAccess

/-- A measured admission-key closure. Counting here is explicit even when
the caller has separately constructed the cached local state. -/
def admissionKey (p : Pool n) (d : LocalData p) (a : LocalAccess (PassiveLocalState.state p d)) :
    Result (ℕ × (ℕ → Result ℕ)) :=
  let size := a.population
  if size.value + 1 ≤ p.palette + 1 then ⟨(p.palette, fun key => ⟨key, 1⟩), size.work + 6⟩
  else ⟨(p.palette + 1, fun key => ⟨if key < p.palette + 1 then key else key + 1, 4⟩), size.work + 6⟩

theorem admissionKey_value (p : Pool n) (d : LocalData p)
    (a : LocalAccess (PassiveLocalState.state p d)) (v : Fin n) (hv : v ∉ p.members)
    (key : ℕ) :
    ((a.admissionKey p d).value.2 key).value = ColourTransport.extend (p.admission v hv).embed key := by
  have hs : a.population.value = p.members.card := population_value a
  simp only [admissionKey, hs]
  unfold Pool.admission
  split
  · rename_i hc
    dsimp only [Pool.admitSized, Pool.append]
    rw [dif_pos hc]
    change key = if _ : key < p.palette + 1 then key else (p.palette + 1) + (key - (p.palette + 1))
    split <;> omega
  · rename_i hc
    dsimp only [Pool.admitSized, Pool.append]
    rw [dif_neg hc]
    change (if key < p.palette + 1 then key else key + 1) =
      if _ : key < p.palette + 1 then key else (p.palette + 1 + 1) + (key - (p.palette + 1))
    split <;> omega

theorem admissionKey_palette (p : Pool n) (d : LocalData p)
    (a : LocalAccess (PassiveLocalState.state p d)) (v : Fin n) (hv : v ∉ p.members) :
    (a.admissionKey p d).value.1 = (p.admission v hv).next.palette := by
  have hs : a.population.value = p.members.card := population_value a
  simp only [admissionKey, hs]
  unfold Pool.admission
  split
  · dsimp only [Pool.admitSized, Pool.append]
  · dsimp only [Pool.admitSized, Pool.append]
theorem admissionKey_get_work (p : Pool n) (d : LocalData p)
    (a : LocalAccess (PassiveLocalState.state p d)) (key : ℕ) :
    ((a.admissionKey p d).value.2 key).work ≤ 4 := by
  unfold admissionKey
  dsimp only
  split <;> norm_num only

theorem admissionKey_work (p : Pool n) (d : LocalData p)
    (a : LocalAccess (PassiveLocalState.state p d)) {A : ℕ} (ha : AccessBound a A) :
    (a.admissionKey p d).work ≤ n * (A + 6) + 8 := by
  have hh := population_work a ha
  unfold admissionKey
  dsimp only
  split <;> dsimp only <;> omega

end LocalAccess

namespace TreeAccess

def admitRoot {t : StoredTree n} (a : TreeAccess t) (v : Fin n) (hv : v ∉ t.pool.members) :
    Result (TreeAccess (t.admitRoot v hv)) := by
  cases a with
  | node identity p d access children =>
    let next := access.admitCached p d v hv
    let get := access.admissionKey p d
    let keys := children.mapKeys (p.admission v hv).embed get.value.2
      (LocalAccess.admissionKey_value p d access v hv)
    let members := Finset.cons v p.members hv
    have hp : get.value.1 = (admissionState p d v hv).pool.palette :=
      LocalAccess.admissionKey_palette p d access v hv
    have hm : members = (admissionState p d v hv).pool.members := by
      exact (Finset.cons_eq_insert v p.members hv).trans (p.admission v hv).members_eq.symm
    let state := next.value.realizeWith get.value.1 members hp hm
    let root := next.value.rebasedWith get.value.1 members hp hm
    let represented := TreeAccess.node identity state.pool ⟨state.rows, state.order⟩ root keys.value.rebased
    have eq : StoredTree.node identity state.pool ⟨state.rows, state.order⟩ keys.value.stored =
        (StoredTree.node identity p d _).admitRoot v hv := by
      rw [keys.value.stored_eq]
      exact congrArg (fun s : State n => StoredTree.node identity s.pool ⟨s.rows, s.order⟩ _)
        (next.value.realizeWith_eq get.value.1 members hp hm)
    exact ⟨represented.transport eq, next.work + get.work + keys.work + 40⟩

theorem admitRoot_bound {t : StoredTree n} (a : TreeAccess t)
    (ha : a.Bound 2) (v : Fin n) (hv : v ∉ t.pool.members) : (a.admitRoot v hv).value.Bound 2 := by
  cases a with
  | node identity p d access children =>
    apply transport_bound
    refine ⟨LocalAccess.rebasedWith_bound _ _ _ _ _ (LocalAccess.admitCached_access p d access v hv), ?_⟩
    exact ChildrenAccess.rebased_bound _ (ChildrenAccess.mapKeys_bound children _ _ _ ha.2)

def admissionBound (n palette children : ℕ) : ℕ :=
  16 * n + 91 + LocalAccess.cacheBound n (palette + 1) 17 + 16 * children

theorem admitRoot_work (identity : ℕ) (p : Pool n) (d : LocalData p)
    (access : LocalAccess (PassiveLocalState.state p d))
    {children : List (ℕ × StoredTree n)} (next : ChildrenAccess children)
    (ha : AccessBound access 2) (v : Fin n) (hv : v ∉ p.members) :
    ((TreeAccess.node identity p d access next).admitRoot v hv).work ≤
      admissionBound n p.palette children.length := by
  have hn := LocalAccess.admitCached_work p d access ha v hv
  have hg := LocalAccess.admissionKey_work p d access ha
  have hk := ChildrenAccess.mapKeys_work next (p.admission v hv).embed
    (access.admissionKey p d).value.2 (LocalAccess.admissionKey_value p d access v hv)
    (LocalAccess.admissionKey_get_work p d access)
  have hp := LocalAccess.cacheBound_mono (n := n) (p.admission v hv).palette_bounds.2 (by rfl : 17 ≤ 17)
  simp only [Nat.reduceAdd] at hn hg hk
  change _ + _ + _ + 40 ≤ _
  unfold admissionBound
  omega

def freshChild (n identity : ℕ) (v : Fin n) : Result (TreeAccess (StoredTree.freshChild n identity v)) :=
  let next := (empty n identity).admitRoot v (by simp [StoredTree.empty, StoredTree.pool, emptyPool])
  ⟨next.value, next.work + 2⟩

theorem freshChild_bound (n identity : ℕ) (v : Fin n) : (freshChild n identity v).value.Bound 2 :=
  admitRoot_bound _ (empty_bound n identity) v _

theorem freshChild_work (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).work ≤ admissionBound n 1 0 + 2 := by
  have hh := admitRoot_work identity (emptyPool n) (emptyData n) (emptyAccess n) .nil
    (by constructor <;> intros <;> norm_num only [emptyAccess]) v
    (by simp [emptyPool])
  exact Nat.add_le_add_right hh 2

end TreeAccess

end SortingAdversary.Optimal.RepresentationWork
