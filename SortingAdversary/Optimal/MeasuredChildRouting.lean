import SortingAdversary.Optimal.MeasuredControllerTypes
import SortingAdversary.Optimal.RepresentationTreeView

/-!
# Actual child search and replacement with counted membership reads

Search preserves the original first matching child and consults its cached
membership cells. Replacement traverses the real stored child spine. All
new index data are taken from represented runtime nodes before proof-only
transport to the reference list.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState StoredRouting
variable {n : ℕ}

structure FoundChild (children : List (ℕ × StoredTree n)) where
  key : ℕ
  tree : StoredTree n
  access : TreeAccess tree
  member : (key, tree) ∈ children
  cached : access.Bound 2

def FoundChild.child {children : List (ℕ × StoredTree n)} (f : FoundChild children) :
    {child // child ∈ children} := ⟨(f.key, f.tree), f.member⟩

def FoundChild.shift {children : List (ℕ × StoredTree n)} (head : ℕ × StoredTree n)
    (f : FoundChild children) : FoundChild (head :: children) where
  key := f.key
  tree := f.tree
  access := f.access
  member := List.mem_cons_of_mem head f.member
  cached := f.cached

theorem commonChild_cons (key : ℕ) (tree : StoredTree n) (rest : List (ℕ × StoredTree n)) (a b : Fin n) :
    commonChild ((key, tree) :: rest) a b =
      if a ∈ tree.pool.members ∧ b ∈ tree.pool.members
      then some ⟨(key, tree), List.mem_cons_self⟩
      else (commonChild rest a b).map (fun f => ⟨f.val, List.mem_cons_of_mem _ f.property⟩) := by
  simp only [commonChild, List.attach_cons, List.find?_cons, List.find?_map, Function.comp_def]
  split
  · rename_i _ he
    rw [if_pos (of_decide_eq_true he)]
  · rename_i _ he
    rw [if_neg (of_decide_eq_false he)]

def TreeAccess.memberTest {t : StoredTree n} (access : TreeAccess t) (a b : Fin n) : Result Bool :=
  let left := access.root.member a
  let right := access.root.member b
  ⟨left.value && right.value, left.work + right.work + 3⟩

theorem TreeAccess.memberTest_value {t : StoredTree n} (access : TreeAccess t) (a b : Fin n) :
    (access.memberTest a b).value = decide (a ∈ t.pool.members ∧ b ∈ t.pool.members) := by
  have hl : (access.root.member a).value = decide (a ∈ t.pool.members) := access.root.member_value a
  have hr : (access.root.member b).value = decide (b ∈ t.pool.members) := access.root.member_value b
  apply Bool.eq_iff_iff.mpr
  simp only [memberTest, hl, hr, Bool.and_eq_true, decide_eq_true_eq]

theorem TreeAccess.memberTest_work {t : StoredTree n} (access : TreeAccess t)
    (ha : access.Bound 2) (a b : Fin n) : (access.memberTest a b).work ≤ 7 := by
  have hl := (access.root_bound ha).member a
  have hr := (access.root_bound ha).member b
  change _ + _ + 3 ≤ _
  omega

namespace ChildrenAccess

def common {children : List (ℕ × StoredTree n)} (access : ChildrenAccess children)
    (ha : access.Bound 2) (a b : Fin n) : Result (Option (FoundChild children)) := by
  cases access with
  | nil => exact ⟨none, 1⟩
  | @cons key tree child rest tail =>
    let test := child.memberTest a b
    if test.value then
      have hm : (key, child.stored) ∈ (key, tree) :: rest := by rw [child.stored_eq]; exact List.mem_cons_self
      exact ⟨some ⟨key, child.stored, child.rebased, hm, child.rebased_bound ha.1⟩, test.work + 17⟩
    else
      let found := tail.common ha.2 a b
      exact ⟨found.value.map (FoundChild.shift (key, tree)), test.work + found.work + 17⟩

theorem common_value {children : List (ℕ × StoredTree n)} (access : ChildrenAccess children)
    (ha : access.Bound 2) (a b : Fin n) :
    (access.common ha a b).value.map FoundChild.child = commonChild children a b := by
  cases access with
  | nil => rfl
  | @cons key tree child rest tail =>
    rw [commonChild_cons]
    unfold common
    dsimp only
    rw [child.memberTest_value]
    split
    · rename_i he
      have hm := of_decide_eq_true he
      simp only [if_pos hm, Option.map_some, FoundChild.child, child.stored_eq]
    · rename_i he
      have hm : ¬ (a ∈ tree.pool.members ∧ b ∈ tree.pool.members) := fun h => he (decide_eq_true h)
      rw [if_neg hm, ← common_value tail ha.2 a b]
      cases (tail.common ha.2 a b).value <;> rfl

theorem common_work {children : List (ℕ × StoredTree n)} (access : ChildrenAccess children)
    (ha : access.Bound 2) (a b : Fin n) : (access.common ha a b).work ≤ 24 * children.length + 1 := by
  cases access with
  | nil => simp only [common, List.length_nil, Nat.mul_zero, Nat.zero_add, le_refl]
  | cons key child tail =>
    have hh := child.memberTest_work ha.1 a b
    have ht := common_work tail ha.2 a b
    unfold common
    dsimp only
    split <;> dsimp only <;> simp only [List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega

def replace {children : List (ℕ × StoredTree n)} (access : ChildrenAccess children)
    (key : ℕ) {next : StoredTree n} (replacement : TreeAccess next) :
    Result (ChildrenAccess (replaceChildren key next children)) := by
  cases access with
  | nil => exact ⟨.nil, 1⟩
  | @cons current tree child rest tail =>
    let later := tail.replace key replacement
    if he : current = key then
      let node := ChildrenAccess.cons current replacement.rebased later.value.rebased
      have eq : (current, replacement.stored) :: later.value.stored = replaceChildren key next ((current, tree) :: rest) := by
        rw [replacement.stored_eq, later.value.stored_eq]
        simp only [replaceChildren, List.map_cons, if_pos he]
      exact ⟨node.transport eq, later.work + 20⟩
    else
      let node := ChildrenAccess.cons current child.rebased later.value.rebased
      have eq : (current, child.stored) :: later.value.stored = replaceChildren key next ((current, tree) :: rest) := by
        rw [child.stored_eq, later.value.stored_eq]
        simp only [replaceChildren, List.map_cons, if_neg he]
      exact ⟨node.transport eq, later.work + 20⟩

theorem replace_bound {children : List (ℕ × StoredTree n)} (access : ChildrenAccess children)
    (key : ℕ) {next : StoredTree n} (replacement : TreeAccess next) {A : ℕ}
    (ha : access.Bound A) (hn : replacement.Bound A) : (access.replace key replacement).value.Bound A := by
  cases access with
  | nil => trivial
  | cons current child tail =>
    unfold replace
    dsimp only
    split <;> apply transport_bound
    · exact ⟨replacement.rebased_bound hn, rebased_bound _ (replace_bound tail key replacement ha.2 hn)⟩
    · exact ⟨child.rebased_bound ha.1, rebased_bound _ (replace_bound tail key replacement ha.2 hn)⟩

theorem replace_work {children : List (ℕ × StoredTree n)} (access : ChildrenAccess children)
    (key : ℕ) {next : StoredTree n} (replacement : TreeAccess next) :
    (access.replace key replacement).work = 20 * children.length + 1 := by
  cases access with
  | nil => rfl
  | cons current child tail =>
    unfold replace
    dsimp only
    split <;> dsimp only <;> rw [replace_work tail key replacement] <;>
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega

end ChildrenAccess

end SortingAdversary.Optimal.RepresentationWork
