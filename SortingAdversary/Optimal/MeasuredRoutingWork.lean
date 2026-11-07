import SortingAdversary.Optimal.MeasuredRouting

/-! # Polynomial work for the complete represented child router -/

namespace SortingAdversary.Optimal.MeasuredController

open PrimitiveWork RepresentationWork PoolState StoredRouting PoolTree.Tree PoolPalette
variable {n : ℕ} {P : LocalProperty n} {Payload : Type*}

def StopBound {stop : Stopper P Payload} (execStop : StopExecutor stop) (B : ℕ) : Prop :=
  ∀ (t : StoredTree n) (access : TreeAccess t) (cached : access.Bound 2)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (ready : AllNodes P t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) (counter : ℕ),
    TreeBounded t.erase → (execStop t access cached hw ho ready a b ha hb hab hba hstop counter).work ≤ B

def routingNodeBound (n B : ℕ) : ℕ :=
  B + LocalAccess.cacheBound n (treeShapeBound n) 16 + 44 * treeShapeBound n + 140

theorem routeFuel_work (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload) (execStop : StopExecutor stop)
    (B : ℕ) (hstop : StopBound execStop B)
    (fuel : ℕ) (t : StoredTree n) (access : TreeAccess t) (cached : access.Bound 2)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (ready : AllNodes P t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (counter : ℕ) (height : t.pool.members.card < fuel) (bounded : TreeBounded t.erase) :
    (routeFuel stop stable delegatePayload execStop fuel t access cached hw ho ready a b ha hb hab hba counter height).work ≤
      fuel * routingNodeBound n B := by
  induction fuel generalizing t with
  | zero => exact False.elim (Nat.not_lt_zero _ height)
  | succ fuel ih =>
    cases access with
    | @node identity p d localAccess children childrenAccess =>
      have hsearch := ChildrenAccess.common_work childrenAccess cached.2 a b
      have hlength : children.length ≤ treeShapeBound n :=
        stored_children_length (.node identity p d children) hw bounded
      have hpalette : p.palette ≤ treeShapeBound n := by
        have hh := stored_palette_size (.node identity p d children) bounded
        change p.palette + 1 ≤ treeShapeBound n at hh
        omega
      have hp : Parts p (StoredTree.erasedChildren children) := by
        apply PoolTree.Tree.parts
        simpa only [StoredTree.erase, StoredTree.erasedChildren] using hw
      rw [routeFuel]
      dsimp only
      split
      · rename_i he
        have hf : commonChild children a b = none := by
          rw [← ChildrenAccess.common_value childrenAccess cached.2 a b, he]
          rfl
        have hprice := hstop (.node identity p d children)
          (.node identity p d localAccess childrenAccess) cached hw ho ready a b ha hb hab hba
          (no_commonChild hp a b ha hb hf) counter bounded
        dsimp only
        have hbudget : B + 24 * children.length + 21 ≤ routingNodeBound n B := by
          unfold routingNodeBound
          omega
        have hmult : routingNodeBound n B ≤ (fuel + 1) * routingNodeBound n B := by
          exact Nat.le_mul_of_pos_left _ (Nat.succ_pos fuel)
        omega
      · rename_i child he
        have hf : commonChild children a b = some child.child := by
          rw [← ChildrenAccess.common_value childrenAccess cached.2 a b, he]
          rfl
        have ctx := childContext identity p d hw ho ready a b hab hba child.child hf
        have smaller : child.tree.pool.members.card < fuel := by
          have hh := ctx.smaller
          change child.tree.pool.members.card < p.members.card at hh
          change p.members.card < fuel + 1 at height
          omega
        have hbnd := childContext_bounded identity p d bounded child.child
        let answer := routeFuel stop stable delegatePayload execStop fuel child.tree child.access child.cached
          ctx.wellFormed ctx.coherent ctx.ready a b ctx.left ctx.right ctx.forward ctx.backward counter smaller
        have hanswer := ih child.tree child.access child.cached ctx.wellFormed ctx.coherent ctx.ready
          ctx.left ctx.right ctx.forward ctx.backward smaller hbnd
        have hupdate := delegate_work identity p d localAccess childrenAccess hp child.child a b
          ctx.left ctx.right hab hba answer.value.core answer.value.access cached.1 cached.2 answer.value.cached
        have hcache := LocalAccess.cacheBound_mono (n := n) hpalette (le_refl 16)
        dsimp only
        dsimp only [answer] at hupdate
        have hbudget : LocalAccess.cacheBound n p.palette 16 + 44 * children.length + 106 ≤
            routingNodeBound n B := by
          unfold routingNodeBound
          omega
        rw [Nat.succ_mul]
        omega

theorem route_work (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload) (execStop : StopExecutor stop)
    (B : ℕ) (hstop : StopBound execStop B)
    (t : StoredTree n) (access : TreeAccess t) (cached : access.Bound 2)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent) (ready : AllNodes P t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (counter : ℕ) (bounded : TreeBounded t.erase) :
    (route stop stable delegatePayload execStop t access cached hw ho ready a b ha hb hab hba counter).work ≤
      (n + 1) * routingNodeBound n B + 2 := by
  exact Nat.add_le_add_right
    (routeFuel_work stop stable delegatePayload execStop B hstop (n + 1) t access cached hw ho ready
      a b ha hb hab hba counter _ bounded) 2

end SortingAdversary.Optimal.MeasuredController
