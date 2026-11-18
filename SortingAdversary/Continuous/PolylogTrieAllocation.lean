import SortingAdversary.Continuous.PolylogRouting

/-!
# Cells allocated by persistent table operations

A cell contains a leaf payload or two child addresses. A shared fill installs
the same child address twice. Updating a location copies a single root path;
the original root and all unaffected subtrees remain readable in the new arena.
The arena's next address counts cumulative allocations, including obsolete
versions, without assuming garbage collection.
-/

namespace SortingAdversary.Continuous.PolylogTrieAllocation

open PolylogRouting (Table)
variable {α : Type}

inductive Cell (α : Type) where
  | leaf (value : α)
  | branch (left right : ℕ)

structure Arena (α : Type) where
  next : ℕ
  read : ℕ → Cell α

/-- Only addresses below the allocation frontier denote initialized cells. -/
inductive Denotes (H : Arena α) : {t : ℕ} → ℕ → Table α t → Prop where
  | leaf {i x} : i < H.next → H.read i = .leaf x → Denotes H i (.leaf x)
  | branch {h i l r} {a b : Table α h} : i < H.next → H.read i = .branch l r →
      Denotes H l a → Denotes H r b → Denotes H i (.node a b)

def Extends (K H : Arena α) := H.next ≤ K.next ∧ ∀ i < H.next, K.read i = H.read i

theorem Extends.refl (H : Arena α) : Extends H H := ⟨le_rfl, fun _ _ => rfl⟩

theorem Extends.trans {J K H : Arena α} (hj : Extends J K) (hk : Extends K H) : Extends J H :=
  ⟨hk.1.trans hj.1, fun i hi => (hj.2 i (hi.trans_le hk.1)).trans (hk.2 i hi)⟩

theorem Denotes.persist {H K : Arena α} {h i} {t : Table α h} (d : Denotes H i t)
    (e : Extends K H) : Denotes K i t := by
  induction d with
  | leaf hi eq => exact .leaf (hi.trans_le e.1) ((e.2 _ hi).trans eq)
  | branch hi eq _ _ a b => exact .branch (hi.trans_le e.1) ((e.2 _ hi).trans eq) a b

def pushCell (H : Arena α) (v : Cell α) : Arena α :=
  ⟨H.next+1, Function.update H.read H.next v⟩

theorem push_extends (H : Arena α) (v : Cell α) : Extends (pushCell H v) H :=
  ⟨Nat.le_succ _, fun i hi => Function.update_of_ne hi.ne ..⟩

@[simp] theorem push_read (H : Arena α) (v : Cell α) : (pushCell H v).read H.next = v :=
  Function.update_self ..

def build (H : Arena α) (v : α) : ℕ → Arena α × ℕ
  | 0 => (pushCell H (.leaf v), H.next)
  | h+1 =>
    let (K,child) := build H v h
    (pushCell K (.branch child child), K.next)

theorem build_spec (H : Arena α) (v : α) (h : ℕ) :
    let (K,i) := build H v h
    Extends K H ∧ Denotes K i (Table.fill v h) ∧ K.next = H.next+(h+1) := by
  induction h with
  | zero => exact ⟨push_extends .., .leaf (Nat.lt_succ_self _) (push_read ..), rfl⟩
  | succ h ih =>
    obtain ⟨ex, rep, size⟩ := ih
    let z := build H v h
    let hh := push_extends z.1 (.branch z.2 z.2)
    exact ⟨hh.trans ex, .branch (Nat.lt_succ_self _) (push_read ..) (rep.persist hh) (rep.persist hh),
      by change (build H v h).1.next+1 = _; omega⟩

/-- The malformed-height branch is unreachable for a represented root. -/
def replace (H : Arena α) (value : α) : ℕ → ℕ → ℕ → Arena α × ℕ
  | 0, _, _ => (pushCell H (.leaf value), H.next)
  | h+1, root, key =>
    match H.read root with
    | .leaf _ => (H,root)
    | .branch l r =>
      if key % 2 = 0 then
        let (K,a) := replace H value h l (key/2)
        (pushCell K (.branch a r), K.next)
      else
        let (K,b) := replace H value h r (key/2)
        (pushCell K (.branch l b), K.next)

theorem replace_spec {H : Arena α} {h i : ℕ} {t : Table α h} (d : Denotes H i t)
    (key : ℕ) (v : α) :
    let (K,j) := replace H v h i key
    Extends K H ∧ Denotes K j (t.put key v).value ∧ K.next = H.next+(h+1) := by
  induction d generalizing key with
  | leaf => exact ⟨push_extends .., .leaf (Nat.lt_succ_self _) (push_read ..), rfl⟩
  | @branch h i l r a b hi eq dl dr il ir =>
    simp only [replace, eq]
    by_cases even : key % 2 = 0
    · simp only [even, if_true, Table.put]
      obtain ⟨eh, dh, sz⟩ := il (key/2)
      let z := replace H v h l (key/2)
      let ex := push_extends z.1 (.branch z.2 r)
      refine ⟨ex.trans eh, .branch (Nat.lt_succ_self _) (push_read ..) (dh.persist ex)
        (dr.persist (ex.trans eh)), ?_⟩
      change (replace H v h l (key/2)).1.next + 1 = _
      omega
    · simp only [even, if_false, Table.put]
      obtain ⟨eh, dh, sz⟩ := ir (key/2)
      let z := replace H v h r (key/2)
      let ex := push_extends z.1 (.branch l z.2)
      refine ⟨ex.trans eh, .branch (Nat.lt_succ_self _) (push_read ..) (dl.persist (ex.trans eh))
        (dh.persist ex), ?_⟩
      change (replace H v h r (key/2)).1.next + 1 = _
      omega

/-- Each *physical* allocation on a persistent trie write is paid for by
the work already charged by the public table operation. -/
theorem replace_budget {H : Arena α} {h i : ℕ} {t : Table α h} (d : Denotes H i t)
    (key : ℕ) (v : α) : (replace H v h i key).1.next ≤ H.next+(t.put key v).work := by
  have sz := (replace_spec d key v).2.2
  rw [sz,Table.put_work]; omega

end SortingAdversary.Continuous.PolylogTrieAllocation
