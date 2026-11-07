import SortingAdversary.Optimal.StoredTree
import SortingAdversary.Optimal.StoppingComparison

/-!
# Routing queries in the actual stored tree

The executable router retains source rows and palette birth order at every
ancestor. Its erasure is exactly the already verified tree replacement.
Local invariants are proof arguments, so they introduce no runtime oracle.
-/

namespace SortingAdversary.Optimal

open PoolState WeakMaps WeakMaps.WeakSystem ControllerRouting Safety
open PoolTree.Tree PoolPalette
variable {n : ℕ}

def LocalData.add (p : Pool n) (d : LocalData p) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins) :
    LocalData (addComparison p a b ha hb hi) :=
  ⟨d.rows.add a b hab, d.order⟩

namespace StoredRouting

abbrev LocalProperty (n : ℕ) := ∀ p : Pool n, LocalData p → Prop

def AllNodes (P : LocalProperty n) : StoredTree n → Prop
  | .node _ p d children => P p d ∧ ∀ a ∈ children, AllNodes P a.2
decreasing_by
  have hh := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at hh
  omega

@[simp] theorem allNodes_node (P : LocalProperty n) (identity : ℕ) (p : Pool n)
    (d : LocalData p) (children : List (ℕ × StoredTree n)) :
    AllNodes P (.node identity p d children) ↔ P p d ∧ ∀ a ∈ children, AllNodes P a.2 := by
  rw [AllNodes]

def semanticChild (a : ℕ × StoredTree n) : ℕ × PoolTree.Tree n := (a.1, a.2.erase)

theorem semanticChild_mem {children : List (ℕ × StoredTree n)} {a : ℕ × StoredTree n}
    (ha : a ∈ children) : semanticChild a ∈ StoredTree.erasedChildren children :=
  List.mem_map.mpr ⟨a, ha, rfl⟩

@[simp] theorem semanticChild_pool (a : ℕ × StoredTree n) :
    (semanticChild a).2.pool = a.2.pool := StoredTree.erase_pool _

def replaceChildren (key : ℕ) (next : StoredTree n) (children : List (ℕ × StoredTree n)) :
    List (ℕ × StoredTree n) := children.map (fun a => (a.1, if a.1 = key then next else a.2))

theorem erased_replaceChildren (key : ℕ) (next : StoredTree n)
    (children : List (ℕ × StoredTree n)) :
    StoredTree.erasedChildren (replaceChildren key next children) =
      PoolTree.Tree.replaceChildren key next.erase (StoredTree.erasedChildren children) := by
  simp only [replaceChildren, PoolTree.Tree.replaceChildren, StoredTree.erasedChildren,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro a ha
  split <;> rfl

def stopNode (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins) : StoredTree n :=
  .node identity (addComparison p a b ha hb hi) (d.add p a b ha hb hab hi) children

@[simp] theorem erase_stopNode (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins) :
    (stopNode identity p d children a b ha hb hab hi).erase =
      PoolTree.Tree.stopNode identity p (StoredTree.erasedChildren children) a b ha hb hi := by
  rw [stopNode, StoredTree.erase]
  rfl

theorem distinct_of_reverse_unknown (p : Pool n) (a b : Fin n)
    (hba : p.system.edge b a ≠ true) : a ≠ b := by
  rintro rfl
  exact hba (p.invariant.closed.refl a)

def delegatedNode (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (h : Parts p (StoredTree.erasedChildren children))
    (target : ℕ × StoredTree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : StoredTree n) : StoredTree n :=
  let target' := semanticChild target
  let ht' := semanticChild_mem ht
  let ha' : a ∈ target'.2.pool.members := by simpa only [target', semanticChild, StoredTree.erase_pool] using ha
  let hb' : b ∈ target'.2.pool.members := by simpa only [target', semanticChild, StoredTree.erase_pool] using hb
  let ham := ((h.members target' ht' a).mp ha').1
  let hbm := ((h.members target' ht' b).mp hb').1
  let hi := retaining_invariant p a b hba (same_child_retains h target' ht' a b ha' hb')
  .node identity (addComparison p a b ham hbm hi)
    (d.add p a b ham hbm (distinct_of_reverse_unknown p a b hba) hi)
    (replaceChildren target.1 next children)

theorem erase_delegatedNode (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (h : Parts p (StoredTree.erasedChildren children))
    (target : ℕ × StoredTree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : StoredTree n) :
    (delegatedNode identity p d children h target ht a b ha hb hba next).erase =
      PoolTree.Tree.delegatedNode identity p (StoredTree.erasedChildren children) h
        (semanticChild target) (semanticChild_mem ht) a b (by simpa using ha) (by simpa using hb)
        hba next.erase := by
  rw [delegatedNode, StoredTree.erase, PoolTree.Tree.delegatedNode]
  exact congrArg (PoolTree.Tree.node identity _) (erased_replaceChildren _ _ _)

def commonChild (children : List (ℕ × StoredTree n)) (a b : Fin n) :
    Option {child // child ∈ children} :=
  children.attach.find? (fun child =>
    decide (a ∈ child.val.2.pool.members ∧ b ∈ child.val.2.pool.members))

theorem commonChild_members {children : List (ℕ × StoredTree n)} {a b : Fin n}
    {child : {child // child ∈ children}} (h : commonChild children a b = some child) :
    a ∈ child.val.2.pool.members ∧ b ∈ child.val.2.pool.members := by
  have hh := List.find?_some (p := fun child : {child // child ∈ children} =>
    decide (a ∈ child.val.2.pool.members ∧ b ∈ child.val.2.pool.members)) h
  exact of_decide_eq_true hh

theorem no_commonChild {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : Parts p (StoredTree.erasedChildren children)) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hn : commonChild children a b = none) :
    ¬ ∃ c, p.pins a = some c ∧ p.pins b = some c := by
  apply PoolTree.Tree.no_commonChild h a b ha hb
  apply List.find?_eq_none.mpr
  intro child hchild
  obtain ⟨old, hold, he⟩ := List.mem_map.mp child.property
  have hh := List.find?_eq_none.mp hn ⟨old, hold⟩ (List.mem_attach _ _)
  intro hm
  apply hh
  have hp := of_decide_eq_true hm
  rw [← he] at hp
  simpa only [StoredTree.erase_pool] using decide_eq_true hp

/-- A same-child update is the only mutation performed by an ancestor. -/
abbrev DelegationStable (P : LocalProperty n) : Prop :=
  ∀ (p : Pool n) (d : LocalData p) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : Invariant (closedAdd p.system a b) p.pins),
    (∃ c, p.pins a = some c ∧ p.pins b = some c) → P p d →
      P (addComparison p a b ha hb hi) (d.add p a b ha hb hab hi)

theorem delegatedNode_allNodes (P : LocalProperty n) (stable : DelegationStable P)
    (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (h : Parts p (StoredTree.erasedChildren children))
    (target : ℕ × StoredTree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : StoredTree n)
    (hold : AllNodes P (.node identity p d children)) (hnext : AllNodes P next) :
    AllNodes P (delegatedNode identity p d children h target ht a b ha hb hba next) := by
  obtain ⟨hp, hc⟩ := (allNodes_node P identity p d children).mp hold
  rw [delegatedNode, allNodes_node]
  constructor
  · apply stable _ _ _ _ _ _ _ _ _ hp
    obtain ⟨c, hca, hcv⟩ := h.pin_witness (semanticChild target) (semanticChild_mem ht)
      a (by simpa using ha)
    obtain ⟨e, heb, hev⟩ := h.pin_witness (semanticChild target) (semanticChild_mem ht)
      b (by simpa using hb)
    have heq : e = c := Fin.ext (hev.trans hcv.symm)
    exact ⟨c, hca, heq ▸ heb⟩
  · intro child hchild
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hchild
    by_cases he : old.1 = target.1
    · simpa only [if_pos he] using hnext
    · simpa only [if_neg he] using hc old ho

structure Answered (P : LocalProperty n) (Payload : Type*) (t : StoredTree n) (a b : Fin n) where
  forward : Bool
  next : StoredTree n
  counter : ℕ
  payload : Payload
  charge : ℚ
  wellFormed : next.erase.WellFormed
  coherent : next.erase.Coherent
  bounded : TreeBounded t.erase → TreeBounded next.erase
  ready : AllNodes P next
  members : next.pool.members = t.pool.members
  edges : next.pool.system.edge =
    (closedAdd t.pool.system (firstLabel a b forward) (secondLabel a b forward)).edge
  retention : (t.erase.count : ℚ) ≤ charge * next.erase.count

abbrev Stopper (P : LocalProperty n) (Payload : Type*) :=
  ∀ (t : StoredTree n), t.erase.WellFormed → t.erase.Coherent → AllNodes P t →
    ∀ (a b : Fin n), a ∈ t.pool.members → b ∈ t.pool.members →
      t.pool.system.edge a b ≠ true → t.pool.system.edge b a ≠ true →
      (¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) →
      ℕ → Answered P Payload t a b

def routeUnknown {P : LocalProperty n} {Payload : Type*}
    (stop : Stopper P Payload) (stable : DelegationStable P)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload)
    (t : StoredTree n) (h : t.erase.WellFormed) (ho : t.erase.Coherent) (ready : AllNodes P t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (counter : ℕ) : Answered P Payload t a b :=
  match t with
  | .node identity p d children =>
    have hw : (PoolTree.Tree.node identity p (StoredTree.erasedChildren children)).WellFormed := by
      simpa only [StoredTree.erase, StoredTree.erasedChildren] using h
    have hc : (PoolTree.Tree.node identity p (StoredTree.erasedChildren children)).Coherent := by
      simpa only [StoredTree.erase, StoredTree.erasedChildren] using ho
    let hp := parts hw
    match found : commonChild children a b with
    | none => stop (.node identity p d children) h ho ready a b ha hb hab hba
        (no_commonChild hp a b ha hb found) counter
    | some child =>
      let hm := commonChild_members found
      let child' := semanticChild child.val
      let hchild := semanticChild_mem child.property
      have hab' : child.val.2.pool.system.edge a b ≠ true := by
        rw [← StoredTree.erase_pool child.val.2]
        change child'.2.pool.system.edge a b ≠ true
        rw [hc.restriction child' hchild a (by simpa [child'] using hm.1) b (by simpa [child'] using hm.2)]
        exact hab
      have hba' : child.val.2.pool.system.edge b a ≠ true := by
        rw [← StoredTree.erase_pool child.val.2]
        change child'.2.pool.system.edge b a ≠ true
        rw [hc.restriction child' hchild b (by simpa [child'] using hm.2) a (by simpa [child'] using hm.1)]
        exact hba
      let result := routeUnknown stop stable delegatePayload child.val.2
        (hp.children_ok child' hchild) (hc.children child' hchild)
        (((allNodes_node P identity p d children).mp ready).2 child.val child.property)
        a b hm.1 hm.2 hab' hba' counter
      let first := firstLabel a b result.forward
      let second := secondLabel a b result.forward
      let hf := first_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hs := second_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hr := reverse_unknown p a b hab hba result.forward
      let next := delegatedNode identity p d children hp child.val child.property
        first second hf hs hr result.next
      have he := erase_delegatedNode identity p d children hp child.val child.property
        first second hf hs hr result.next
      { forward := result.forward
        next := next
        counter := result.counter
        payload := delegatePayload identity first second result.payload
        charge := result.charge
        wellFormed := by
          rw [he]
          exact delegatedNode_wellFormed identity p _ hp child' hchild first second
            (by simpa [child'] using hf) (by simpa [child'] using hs) hr result.next.erase result.wellFormed
            (by simpa only [child', semanticChild, StoredTree.erase_pool] using result.members)
        coherent := by
          rw [he]
          exact delegatedNode_coherent identity p _ hp hc child' hchild first second
            (by simpa [child'] using hf) (by simpa [child'] using hs) hr result.next.erase result.coherent
            (by simpa only [child', semanticChild, StoredTree.erase_pool] using result.members)
            (by
              dsimp only [child', semanticChild]
              rw [StoredTree.erase_pool, StoredTree.erase_pool]
              exact result.edges)
        bounded := by
          intro hbnd
          rw [he]
          have hbnd' : TreeBounded (PoolTree.Tree.node identity p (StoredTree.erasedChildren children)) := by
            simpa only [StoredTree.erase, StoredTree.erasedChildren] using hbnd
          exact delegatedNode_bounded identity p _ hp child' hchild first second
            (by simpa [child'] using hf) (by simpa [child'] using hs) hr result.next.erase hbnd'
            (result.bounded (((treeBounded_node_iff _ _ _).mp hbnd').2 child' hchild))
        ready := delegatedNode_allNodes P stable identity p d children hp child.val child.property
          first second hf hs hr result.next ready result.ready
        members := rfl
        edges := rfl
        retention := by
          rw [he, StoredTree.erase]
          exact delegatedNode_retention identity p _ hp child' hchild first second
            (by simpa [child'] using hf) (by simpa [child'] using hs) hr result.next.erase result.charge result.retention }
termination_by sizeOf t
decreasing_by
  have hh := List.sizeOf_lt_of_mem child.property
  rcases child with ⟨⟨key, subtree⟩, hm⟩
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at hh
  omega

end StoredRouting
end SortingAdversary.Optimal
