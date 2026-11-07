import SortingAdversary.Optimal.MeasuredDelegation
import SortingAdversary.Optimal.RepresentationTreeBounds

/-!
# Counted recursion through the actual stored tree

The search reads cached child membership cells. Every ancestor is rebuilt
with the measured comparison update and a counted replacement scan. The
reference router occurs only in the result's equality certificate; payloads
and accounting products are absent from the executable value.
-/

namespace SortingAdversary.Optimal.MeasuredController

open PrimitiveWork RepresentationWork PoolState StoredRouting PoolTree.Tree PoolPalette
variable {n : ℕ} {P : LocalProperty n} {Payload : Type*}

structure ChildContext (P : LocalProperty n) (p : Pool n)
    {children : List (ℕ × StoredTree n)} (child : {c // c ∈ children}) (a b : Fin n) : Prop where
  wellFormed : child.val.2.erase.WellFormed
  coherent : child.val.2.erase.Coherent
  ready : AllNodes P child.val.2
  left : a ∈ child.val.2.pool.members
  right : b ∈ child.val.2.pool.members
  forward : child.val.2.pool.system.edge a b ≠ true
  backward : child.val.2.pool.system.edge b a ≠ true
  smaller : child.val.2.pool.members.card < p.members.card

theorem childContext (identity : ℕ) (p : Pool n) (d : LocalData p)
    {children : List (ℕ × StoredTree n)}
    (hw : (StoredTree.node identity p d children).erase.WellFormed)
    (ho : (StoredTree.node identity p d children).erase.Coherent)
    (ready : AllNodes P (.node identity p d children))
    (a b : Fin n) (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true)
    (child : {c // c ∈ children}) (found : commonChild children a b = some child) :
    ChildContext P p child a b := by
  rw [StoredTree.erase] at hw ho
  change (PoolTree.Tree.node identity p (StoredTree.erasedChildren children)).WellFormed at hw
  change (PoolTree.Tree.node identity p (StoredTree.erasedChildren children)).Coherent at ho
  have hp := parts hw
  have hm := commonChild_members found
  have mem := semanticChild_mem child.property
  have hleft : a ∈ (semanticChild child.val).2.pool.members := by simpa using hm.1
  have hright : b ∈ (semanticChild child.val).2.pool.members := by simpa using hm.2
  refine ⟨hp.children_ok _ mem, ho.children _ mem,
    ((allNodes_node P identity p d children).mp ready).2 _ child.property,
    hm.1, hm.2, ?_, ?_, ?_⟩
  · rw [← StoredTree.erase_pool child.val.2]
    change (semanticChild child.val).2.pool.system.edge a b ≠ true
    rw [ho.restriction (semanticChild child.val) mem a hleft b hright]
    exact hab
  · rw [← StoredTree.erase_pool child.val.2]
    change (semanticChild child.val).2.pool.system.edge b a ≠ true
    rw [ho.restriction (semanticChild child.val) mem b hright a hleft]
    exact hba
  · simpa only [semanticChild_pool] using PoolTreeAccounting.child_size_lt hw (semanticChild child.val) mem

theorem childContext_bounded (identity : ℕ) (p : Pool n) (d : LocalData p)
    {children : List (ℕ × StoredTree n)}
    (hb : TreeBounded (StoredTree.node identity p d children).erase)
    (child : {c // c ∈ children}) : TreeBounded child.val.2.erase := by
  rw [StoredTree.erase] at hb
  exact ((treeBounded_node_iff ..).mp hb).2 (semanticChild child.val) (semanticChild_mem child.property)

theorem route_none (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload)
    (identity : ℕ) (p : Pool n) (d : LocalData p) (children : List (ℕ × StoredTree n))
    (hw : (StoredTree.node identity p d children).erase.WellFormed)
    (ho : (StoredTree.node identity p d children).erase.Coherent)
    (ready : AllNodes P (.node identity p d children))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, p.pins a = some c ∧ p.pins b = some c)
    (counter : ℕ) (found : commonChild children a b = none) :
    Core.ofAnswered (routeUnknown stop stable delegatePayload (.node identity p d children)
      hw ho ready a b ha hb hab hba counter) =
      Core.ofAnswered (stop (.node identity p d children) hw ho ready a b ha hb hab hba hstop counter) := by
  erw [StoredRouting.routeUnknown.eq_1]
  split
  · rfl
  · rename_i child he
    have hh := found.symm.trans he
    cases hh

theorem route_some (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload)
    (identity : ℕ) (p : Pool n) (d : LocalData p) (children : List (ℕ × StoredTree n))
    (hw : (StoredTree.node identity p d children).erase.WellFormed)
    (ho : (StoredTree.node identity p d children).erase.Coherent)
    (ready : AllNodes P (.node identity p d children))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true)
    (counter : ℕ) (child : {c // c ∈ children})
    (found : commonChild children a b = some child)
    (hp : Parts p (StoredTree.erasedChildren children)) (ctx : ChildContext P p child a b) :
    Core.ofAnswered (routeUnknown stop stable delegatePayload (.node identity p d children)
      hw ho ready a b ha hb hab hba counter) =
      delegateCore identity p d hp child a b ctx.left ctx.right hab hba
        (Core.ofAnswered (routeUnknown stop stable delegatePayload child.val.2 ctx.wellFormed
          ctx.coherent ctx.ready a b ctx.left ctx.right ctx.forward ctx.backward counter)) := by
  erw [StoredRouting.routeUnknown.eq_1]
  split
  · rename_i he
    have hh := he.symm.trans found
    cases hh
  · rename_i next he
    have hh : next = child := Option.some.inj (he.symm.trans found)
    subst next
    rfl

def routeFuel (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload) (execStop : StopExecutor stop)
    (fuel : ℕ) (t : StoredTree n) (access : TreeAccess t) (cached : access.Bound 2)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (ready : AllNodes P t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (counter : ℕ) (height : t.pool.members.card < fuel) :
    Result (Output (Core.ofAnswered
      (routeUnknown stop stable delegatePayload t hw ho ready a b ha hb hab hba counter))) := by
  cases fuel with
  | zero => exact False.elim (Nat.not_lt_zero _ height)
  | succ fuel =>
    cases access with
    | @node identity p d localAccess children childrenAccess =>
      have parts : Parts p (StoredTree.erasedChildren children) := by
        apply PoolTree.Tree.parts
        simpa only [StoredTree.erase, StoredTree.erasedChildren] using hw
      let found := childrenAccess.common cached.2 a b
      match hm : found.value with
      | none =>
        have he : commonChild children a b = none := by
          rw [← ChildrenAccess.common_value childrenAccess cached.2 a b]
          change found.value.map FoundChild.child = none
          rw [hm]; rfl
        have hstop := no_commonChild parts a b ha hb he
        let answer := execStop (.node identity p d children)
          (.node identity p d localAccess childrenAccess) cached hw ho ready a b ha hb hab hba hstop counter
        exact ⟨{
          core := answer.value.core
          access := answer.value.access
          actual := answer.value.actual.trans (route_none stop stable delegatePayload identity p d children
            hw ho ready a b ha hb hab hba hstop counter he).symm
          cached := answer.value.cached }, found.work + answer.work + 20⟩
      | some child =>
        have he : commonChild children a b = some child.child := by
          rw [← ChildrenAccess.common_value childrenAccess cached.2 a b]
          change found.value.map FoundChild.child = some child.child
          rw [hm]; rfl
        have ctx := childContext identity p d hw ho ready a b hab hba child.child he
        have smaller : child.tree.pool.members.card < fuel := by
          have hc := ctx.smaller
          change child.tree.pool.members.card < p.members.card at hc
          change p.members.card < fuel + 1 at height
          omega
        let answer := routeFuel stop stable delegatePayload execStop fuel child.tree child.access
          child.cached ctx.wellFormed ctx.coherent ctx.ready a b ctx.left ctx.right ctx.forward ctx.backward counter smaller
        let updated := delegate identity p d localAccess childrenAccess parts child.child a b
          ctx.left ctx.right hab hba answer.value.core answer.value.access cached.1 cached.2 answer.value.cached
        have exactCore : delegateCore identity p d parts child.child a b ctx.left ctx.right hab hba answer.value.core =
            Core.ofAnswered (routeUnknown stop stable delegatePayload (.node identity p d children)
              hw ho ready a b ha hb hab hba counter) := by
          rw [answer.value.actual]
          exact (route_some stop stable delegatePayload identity p d children hw ho ready a b ha hb hab hba
            counter child.child he parts ctx).symm
        exact ⟨{
          core := updated.value.core
          access := updated.value.access
          actual := updated.value.actual.trans exactCore
          cached := updated.value.cached }, found.work + answer.work + updated.work + 20⟩
termination_by fuel

def route (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload) (execStop : StopExecutor stop) :
    RouteExecutor stop stable delegatePayload := fun t access cached hw ho ready a b ha hb hab hba counter =>
  let answer := routeFuel stop stable delegatePayload execStop (n + 1) t access cached hw ho ready a b ha hb hab hba counter
    (by have h := Finset.card_le_univ t.pool.members; simpa only [Fintype.card_fin] using Nat.lt_succ_of_le h)
  ⟨answer.value, answer.work + 2⟩

end SortingAdversary.Optimal.MeasuredController
