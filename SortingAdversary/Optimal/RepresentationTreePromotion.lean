import SortingAdversary.Optimal.RepresentationPromotionKeys
import SortingAdversary.Optimal.StoredPromotion
import SortingAdversary.Optimal.TreeChronology

/-!
# Measured destination admission in the actual child list

The child-list traversal transports every key and admits the label only in
the matching existing child. A separate measured destination scan decides
whether a fresh child is appended. All returned getter records refer to the
same actual stored-tree updates used by the adversary.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState

variable {n : ℕ}

def rootChildrenLength (t : StoredTree n) : ℕ :=
  match t with
  | .node _ _ _ children => children.length

theorem TreeAccess.admitRoot_work_all {t : StoredTree n} (a : TreeAccess t)
    (ha : a.Bound 2) (v : Fin n) (hv : v ∉ t.pool.members) :
    (a.admitRoot v hv).work ≤ TreeAccess.admissionBound n t.pool.palette (rootChildrenLength t) := by
  cases a with
  | node identity p d access children => exact TreeAccess.admitRoot_work identity p d access children ha.1 v hv

theorem TreeAccess.admissionBound_mono {n P Q M N : ℕ} (hp : P ≤ Q) (hm : M ≤ N) :
    admissionBound n P M ≤ admissionBound n Q N := by
  unfold admissionBound
  have hcache := LocalAccess.cacheBound_mono (n := n) (Nat.succ_le_succ hp) (le_refl 17)
  simp only [Nat.succ_eq_add_one] at hcache
  have hmul := Nat.mul_le_mul_left 16 hm
  omega

namespace ChildrenAccess

def targets (get : ℕ → Result ℕ) (destination : ℕ) (v : Fin n)
    (ts : List (ℕ × StoredTree n)) (unused : ∀ a ∈ ts, v ∉ a.2.pool.members) :
    List (ℕ × StoredTree n) :=
  match ts with
  | [] => []
  | (key, tree) :: rest =>
    ((get key).value, if (get key).value = destination
      then tree.admitRoot v (unused _ (List.mem_cons_self ..)) else tree) ::
      targets get destination v rest (fun a ha => unused a (List.mem_cons_of_mem _ ha))

theorem targets_length (get : ℕ → Result ℕ) (destination : ℕ) (v : Fin n)
    (ts : List (ℕ × StoredTree n)) (unused : ∀ a ∈ ts, v ∉ a.2.pool.members) :
    (targets get destination v ts unused).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons a rest ih => cases a; simp only [targets, List.length_cons, ih]

theorem targets_map (get : ℕ → Result ℕ) (destination : ℕ) (v : Fin n)
    (ts : List (ℕ × StoredTree n)) (unused : ∀ a ∈ ts, v ∉ a.2.pool.members) :
    targets get destination v ts unused = ts.attach.map (fun a =>
      ((get a.val.1).value, if (get a.val.1).value = destination
        then a.val.2.admitRoot v (unused a.val a.property) else a.val.2)) := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | mk key tree =>
      simp only [targets, List.attach_cons, List.map_cons, List.map_map, ih]
      rfl

def promoteTargets {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (get : ℕ → Result ℕ) (destination : ℕ) (v : Fin n)
    (unused : ∀ entry ∈ ts, v ∉ entry.2.pool.members) :
    Result (ChildrenAccess (targets get destination v ts unused)) := by
  cases a with
  | nil => exact ⟨.nil, 1⟩
  | @cons key tree child remaining rest =>
    let nextKey := get key
    let tail := rest.promoteTargets get destination v (fun a ha => unused a (List.mem_cons_of_mem _ ha))
    if hs : nextKey.value = destination then
      let admitted := child.admitRoot v (unused _ (List.mem_cons_self ..))
      have eq : (nextKey.value, admitted.value.stored) :: tail.value.stored =
          targets get destination v ((key, tree) :: remaining) unused := by
        rw [admitted.value.stored_eq, tail.value.stored_eq]
        simp only [targets, nextKey, if_pos hs]
      exact ⟨(ChildrenAccess.cons nextKey.value admitted.value.rebased tail.value.rebased).transport eq,
        nextKey.work + admitted.work + tail.work + 20⟩
    else
      have eq : (nextKey.value, child.stored) :: tail.value.stored =
          targets get destination v ((key, tree) :: remaining) unused := by
        rw [child.stored_eq, tail.value.stored_eq]
        simp only [targets, nextKey, if_neg hs]
      exact ⟨(ChildrenAccess.cons nextKey.value child.rebased tail.value.rebased).transport eq,
        nextKey.work + tail.work + 20⟩

theorem promoteTargets_bound {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (get : ℕ → Result ℕ) (destination : ℕ) (v : Fin n)
    (unused : ∀ entry ∈ ts, v ∉ entry.2.pool.members) (ha : a.Bound 2) :
    (a.promoteTargets get destination v unused).value.Bound 2 := by
  cases a with
  | nil => trivial
  | cons key child rest =>
    unfold promoteTargets
    dsimp only
    split
    · apply transport_bound
      exact ⟨TreeAccess.rebased_bound _ (TreeAccess.admitRoot_bound child ha.1 v _),
        rebased_bound _ (promoteTargets_bound rest get destination v _ ha.2)⟩
    · apply transport_bound
      exact ⟨child.rebased_bound ha.1, rebased_bound _ (promoteTargets_bound rest get destination v _ ha.2)⟩

theorem promoteTargets_work {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (get : ℕ → Result ℕ) (destination : ℕ) (v : Fin n)
    (unused : ∀ entry ∈ ts, v ∉ entry.2.pool.members) (ha : a.Bound 2)
    {C P M : ℕ} (hc : ∀ key, (get key).work ≤ C)
    (hp : ∀ entry ∈ ts, entry.2.pool.palette ≤ P)
    (hm : ∀ entry ∈ ts, rootChildrenLength entry.2 ≤ M) :
    (a.promoteTargets get destination v unused).work ≤
      ts.length * (C + TreeAccess.admissionBound n P M + 20) + 1 := by
  cases a with
  | nil => simp only [promoteTargets, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons key child rest =>
    have hh := TreeAccess.admitRoot_work_all child ha.1 v (unused _ (List.mem_cons_self ..))
    have hsmall := TreeAccess.admissionBound_mono (n := n) (hp _ (List.mem_cons_self ..)) (hm _ (List.mem_cons_self ..))
    dsimp only at hsmall
    have ht := promoteTargets_work rest get destination v
      (fun a h => unused a (List.mem_cons_of_mem _ h)) ha.2 hc
      (fun a h => hp a (List.mem_cons_of_mem _ h)) (fun a h => hm a (List.mem_cons_of_mem _ h))
    have hk := hc key
    unfold promoteTargets
    dsimp only
    split <;> dsimp only <;> simp only [List.length_cons, Nat.add_mul, one_mul] <;> omega

theorem targets_promotedChildren {s : State n} {ts : List (ℕ × StoredTree n)}
    (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c) (keys : PromotionKeys r) :
    targets keys.key keys.destination v ts (StoredTree.child_unused parts v hv) =
      StoredTree.promotedChildren parts v hv c r := by
  rw [targets_map]
  unfold StoredTree.promotedChildren
  apply List.map_congr_left
  intro a ha
  rw [keys.key_value, keys.destination_value]
  rfl

def promoteChildren {s : State n} {ts : List (ℕ × StoredTree n)}
    (a : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c) (keys : PromotionKeys r) :
    Result (ChildrenAccess (StoredTree.promotedChildren parts v hv c r)) :=
  let next := a.promoteTargets keys.key keys.destination v (StoredTree.child_unused parts v hv)
  ⟨next.value.transport (targets_promotedChildren parts v hv c r keys), next.work⟩

theorem promoteChildren_bound {s : State n} {ts : List (ℕ × StoredTree n)}
    (a : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c) (keys : PromotionKeys r) (ha : a.Bound 2) :
    (a.promoteChildren parts v hv c r keys).value.Bound 2 :=
  transport_bound _ _ (promoteTargets_bound a keys.key keys.destination v _ ha)

theorem promoteChildren_work {s : State n} {ts : List (ℕ × StoredTree n)}
    (a : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c) (keys : PromotionKeys r) (ha : a.Bound 2)
    {C P M : ℕ} (hc : keys.Bound C)
    (hp : ∀ entry ∈ ts, entry.2.pool.palette ≤ P)
    (hm : ∀ entry ∈ ts, rootChildrenLength entry.2 ≤ M) :
    (a.promoteChildren parts v hv c r keys).work ≤
      ts.length * (C + TreeAccess.admissionBound n P M + 20) + 1 :=
  promoteTargets_work a keys.key keys.destination v _ ha hc hp hm

def destination {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (get : ℕ → Result ℕ) (dest : ℕ) : Result Bool :=
  match a with
  | .nil => ⟨false, 1⟩
  | .cons key _ rest =>
    let nextKey := get key
    if nextKey.value = dest then ⟨true, nextKey.work + 3⟩
    else
      let tail := rest.destination get dest
      ⟨tail.value, nextKey.work + tail.work + 3⟩

theorem destination_value {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (get : ℕ → Result ℕ) (dest : ℕ) :
    (a.destination get dest).value = ts.any (fun x => decide ((get x.1).value = dest)) := by
  cases a with
  | nil => rfl
  | cons key child rest =>
    simp only [destination, List.any_cons]
    split <;> simp_all only [decide_true, decide_false, Bool.true_or, Bool.false_or, destination_value rest]

theorem destination_work {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    (get : ℕ → Result ℕ) (dest : ℕ) {C : ℕ} (hc : ∀ key, (get key).work ≤ C) :
    (a.destination get dest).work ≤ ts.length * (C + 3) + 1 := by
  cases a with
  | nil => simp only [destination, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons key child rest =>
    have hk := hc key
    have ht := destination_work rest get dest hc
    simp only [destination, List.length_cons, Nat.add_mul, one_mul]
    split <;> dsimp only <;> omega

theorem destination_actual {s : State n} {ts : List (ℕ × StoredTree n)} (a : ChildrenAccess ts)
    {v : Fin n} {c : Fin (s.pool.palette + 1)}
    {r : Promotion.Result s.pool.system s.pool.pins v c} (keys : PromotionKeys r) :
    (a.destination keys.key keys.destination).value =
      PoolTree.Tree.destinationExists r (StoredTree.erasedChildren ts) := by
  rw [destination_value]
  simp only [StoredTree.erasedChildren, PoolTree.Tree.destinationExists, List.any_map,
    Function.comp_def, keys.key_value, keys.destination_value]

end ChildrenAccess

namespace TreeAccess

def promotedNode {s : State n} (identity : ℕ) {ts : List (ℕ × StoredTree n)}
    (children : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c)
    (data : LocalData (s.pool.installPromotion v hv c r))
    (access : LocalAccess (PassiveLocalState.state (s.pool.installPromotion v hv c r) data))
    (keys : PromotionKeys r) (counter : ℕ) :
    Result (TreeAccess (StoredTree.promotedNode identity s.pool ts parts v hv c r data counter) × ℕ) :=
  let old := children.promoteChildren parts v hv c r keys
  let seen := children.destination keys.key keys.destination
  if he : seen.value = true then
    have actual : PoolTree.Tree.destinationExists r (StoredTree.erasedChildren ts) = true :=
      (children.destination_actual keys).symm.trans he
    let node := pack identity access keys.palette s.pool.members keys.palette_value rfl old.value
    have eq : StoredTree.node identity (s.pool.installPromotion v hv c r) data
        (StoredTree.promotedChildren parts v hv c r) =
        StoredTree.promotedNode identity s.pool ts parts v hv c r data counter := by
      simp only [StoredTree.promotedNode, if_pos actual]
    ⟨(node.value.transport eq, counter), old.work + seen.work + node.work + 8⟩
  else
    have actual : PoolTree.Tree.destinationExists r (StoredTree.erasedChildren ts) ≠ true := by
      rw [← children.destination_actual keys]
      exact he
    let fresh := freshChild n counter v
    let singleton := ChildrenAccess.cons keys.destination fresh.value.rebased .nil
    have one_eq : [(keys.destination, fresh.value.stored)] =
        [(r.destination.val, StoredTree.freshChild n counter v)] := by
      rw [keys.destination_value, fresh.value.stored_eq]
    let joined := old.value.append (singleton.transport one_eq)
    let node := pack identity access keys.palette s.pool.members keys.palette_value rfl joined.value
    have eq : StoredTree.node identity (s.pool.installPromotion v hv c r) data
        (StoredTree.promotedChildren parts v hv c r ++ [(r.destination.val, StoredTree.freshChild n counter v)]) =
        StoredTree.promotedNode identity s.pool ts parts v hv c r data counter := by
      simp only [StoredTree.promotedNode, if_neg actual]
    ⟨(node.value.transport eq, counter + 1),
      old.work + seen.work + fresh.work + joined.work + node.work + 8⟩

theorem promotedNode_bound {s : State n} (identity : ℕ) {ts : List (ℕ × StoredTree n)}
    (children : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c)
    (data : LocalData (s.pool.installPromotion v hv c r))
    (access : LocalAccess (PassiveLocalState.state (s.pool.installPromotion v hv c r) data))
    (keys : PromotionKeys r) (counter : ℕ) (ha : AccessBound access 2) (hch : children.Bound 2) :
    (promotedNode identity children parts v hv c r data access keys counter).value.1.Bound 2 := by
  have ho := children.promoteChildren_bound parts v hv c r keys hch
  unfold promotedNode
  dsimp only
  split
  · apply transport_bound
    exact pack_bound _ _ _ _ _ _ _ ha ho
  · apply transport_bound
    apply pack_bound _ _ _ _ _ _ _ ha
    apply ChildrenAccess.append_bound _ _ ho
    apply ChildrenAccess.transport_bound
    exact ⟨(freshChild_bound n counter v |> rebased_bound _), trivial⟩

theorem promotedNode_counter {s : State n} (identity : ℕ) {ts : List (ℕ × StoredTree n)}
    (children : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c)
    (data : LocalData (s.pool.installPromotion v hv c r))
    (access : LocalAccess (PassiveLocalState.state (s.pool.installPromotion v hv c r) data))
    (keys : PromotionKeys r) (counter : ℕ) :
    (promotedNode identity children parts v hv c r data access keys counter).value.2 =
      TreeChronology.nextIdentityAfter r (StoredTree.erasedChildren ts) counter := by
  unfold promotedNode TreeChronology.nextIdentityAfter
  dsimp only
  split
  · rename_i he
    rw [← children.destination_actual keys, if_pos he]
  · rename_i he
    rw [← children.destination_actual keys, if_neg he]

def promotionBound (n C P M size : ℕ) : ℕ :=
  size * (C + admissionBound n P M + 20) + 1 + size * (C + 3) + 1 +
    admissionBound n 1 0 + 2 + 12 * size + 1 + 48

theorem promotedNode_work {s : State n} (identity : ℕ) {ts : List (ℕ × StoredTree n)}
    (children : ChildrenAccess ts) (parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren ts))
    (v : Fin n) (hv : s.pool.pins v = none) (c : Fin (s.pool.palette + 1))
    (r : Promotion.Result s.pool.system s.pool.pins v c)
    (data : LocalData (s.pool.installPromotion v hv c r))
    (access : LocalAccess (PassiveLocalState.state (s.pool.installPromotion v hv c r) data))
    (keys : PromotionKeys r) (counter : ℕ) (hch : children.Bound 2)
    {C P M : ℕ} (hc : keys.Bound C)
    (hp : ∀ entry ∈ ts, entry.2.pool.palette ≤ P)
    (hm : ∀ entry ∈ ts, rootChildrenLength entry.2 ≤ M) :
    (promotedNode identity children parts v hv c r data access keys counter).work ≤
      promotionBound n C P M ts.length := by
  have ho := children.promoteChildren_work parts v hv c r keys hch hc hp hm
  have he := children.destination_work keys.key keys.destination hc
  have hf := freshChild_work n counter v
  unfold promotedNode
  dsimp only
  split
  · dsimp only
    dsimp only [pack]
    unfold promotionBound
    omega
  · dsimp only
    dsimp only [pack]
    rw [ChildrenAccess.append_work]
    simp only [StoredTree.promotedChildren, List.length_map, List.length_attach]
    unfold promotionBound
    omega

end TreeAccess

end SortingAdversary.Optimal.RepresentationWork
