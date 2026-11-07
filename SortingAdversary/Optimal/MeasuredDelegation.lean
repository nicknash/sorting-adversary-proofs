import SortingAdversary.Optimal.MeasuredChildRouting
import SortingAdversary.Optimal.ComparedWork

/-! # Counted ancestor update after a delegated answer -/

namespace SortingAdversary.Optimal.MeasuredController

open PrimitiveWork RepresentationWork WidthRepair PoolState StoredRouting
open PoolTree.Tree ControllerRouting Safety
variable {n : ℕ}

/-- Reference projection only: runtime implementations reconstruct this
node from cached comparison cells and the measured replacement list. -/
noncomputable def delegateCore (identity : ℕ) (p : Pool n) (d : LocalData p)
    {children : List (ℕ × StoredTree n)} (parts : Parts p (StoredTree.erasedChildren children))
    (target : {child // child ∈ children}) (a b : Fin n)
    (ha : a ∈ target.val.2.pool.members) (hb : b ∈ target.val.2.pool.members)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true) (core : Core n) : Core n :=
  ⟨core.forward,
    delegatedNode identity p d children parts target.val target.property
      (firstLabel a b core.forward) (secondLabel a b core.forward)
      (first_member _ a b ha hb core.forward) (second_member _ a b ha hb core.forward)
      (reverse_unknown p a b hab hba core.forward) core.next,
    core.counter⟩

def delegate (identity : ℕ) (p : Pool n) (d : LocalData p)
    (access : LocalAccess (PassiveLocalState.state p d))
    {children : List (ℕ × StoredTree n)} (ch : ChildrenAccess children)
    (parts : Parts p (StoredTree.erasedChildren children))
    (target : {child // child ∈ children}) (a b : Fin n)
    (ha : a ∈ target.val.2.pool.members) (hb : b ∈ target.val.2.pool.members)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true)
    (core : Core n) (nextAccess : TreeAccess core.next)
    (haccess : AccessBound access 2) (hch : ch.Bound 2) (hnext : nextAccess.Bound 2) :
    Result (Output (delegateCore identity p d parts target a b ha hb hab hba core)) :=
  let first := firstLabel a b core.forward
  let second := secondLabel a b core.forward
  have hf := first_member target.val.2.pool a b ha hb core.forward
  have hs := second_member target.val.2.pool a b ha hb core.forward
  have hf' : first ∈ (semanticChild target.val).2.pool.members := by simpa using hf
  have hs' : second ∈ (semanticChild target.val).2.pool.members := by simpa using hs
  have hfm : first ∈ p.members := ((parts.members _ (semanticChild_mem target.property) first).mp hf').1
  have hsm : second ∈ p.members := ((parts.members _ (semanticChild_mem target.property) second).mp hs').1
  have hr : p.system.edge second first ≠ true := reverse_unknown p a b hab hba core.forward
  have hi := retaining_invariant p first second hr
    (same_child_retains parts _ (semanticChild_mem target.property) first second hf' hs')
  let compared := ComparedWork.compare access first second hfm hsm
    (distinct_of_reverse_unknown p first second hr) hi p.palette p.members rfl rfl
  let replaced := ch.replace target.val.1 nextAccess
  let packed := TreeAccess.pack identity compared.value.access compared.value.state.pool.palette
    compared.value.state.pool.members rfl rfl replaced.value
  have hn : packed.value.stored = (delegateCore identity p d parts target a b ha hb hab hba core).next := by
    rw [packed.value.stored_eq]
    change StoredRepair.node identity compared.value.state (replaceChildren target.val.1 core.next children) = _
    rw [compared.value.actual]
    rfl
  ⟨{
    core := ⟨core.forward, packed.value.stored, core.counter⟩
    access := packed.value.rebased
    actual := by
      change (⟨core.forward, packed.value.stored, core.counter⟩ : Core n) = _
      rw [hn]
      rfl
    cached := packed.value.rebased_bound (TreeAccess.pack_bound _ _ _ _ _ _ _ compared.value.cached
      (ChildrenAccess.replace_bound ch target.val.1 nextAccess hch hnext)) },
    compared.work + replaced.work + packed.work + 20⟩

theorem delegate_work (identity : ℕ) (p : Pool n) (d : LocalData p)
    (access : LocalAccess (PassiveLocalState.state p d))
    {children : List (ℕ × StoredTree n)} (ch : ChildrenAccess children)
    (parts : Parts p (StoredTree.erasedChildren children))
    (target : {child // child ∈ children}) (a b : Fin n)
    (ha : a ∈ target.val.2.pool.members) (hb : b ∈ target.val.2.pool.members)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true)
    (core : Core n) (nextAccess : TreeAccess core.next)
    (haccess : AccessBound access 2) (hch : ch.Bound 2) (hnext : nextAccess.Bound 2) :
    (delegate identity p d access ch parts target a b ha hb hab hba core nextAccess haccess hch hnext).work ≤
      LocalAccess.cacheBound n p.palette 16 + 20 * children.length + 85 := by
  have hf : firstLabel a b core.forward ∈ (semanticChild target.val).2.pool.members := by
    simpa using first_member target.val.2.pool a b ha hb core.forward
  have hs : secondLabel a b core.forward ∈ (semanticChild target.val).2.pool.members := by
    simpa using second_member target.val.2.pool a b ha hb core.forward
  have hfm := ((parts.members _ (semanticChild_mem target.property) _).mp hf).1
  have hsm := ((parts.members _ (semanticChild_mem target.property) _).mp hs).1
  have hr := reverse_unknown p a b hab hba core.forward
  have hi := retaining_invariant p _ _ hr
    (same_child_retains parts _ (semanticChild_mem target.property) _ _ hf hs)
  have hc := ComparedWork.compare_work_le access haccess
    (firstLabel a b core.forward) (secondLabel a b core.forward) hfm hsm
    (distinct_of_reverse_unknown p _ _ hr) hi p.palette p.members rfl rfl
  unfold delegate
  dsimp only
  simp only [Nat.reduceMul, Nat.reduceAdd] at hc
  rw [TreeAccess.pack_work, ChildrenAccess.replace_work]
  omega

def Output.transport {expected next : Core n} (he : expected = next) (out : Output expected) :
    Output next := he ▸ out

end SortingAdversary.Optimal.MeasuredController
