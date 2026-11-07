import SortingAdversary.Optimal.TreeReplacement
import SortingAdversary.Optimal.PoolPalette

/-!
# Executable recursive routing of an unknown physical comparison

The router descends through the actual child containing both original labels.
It calls the supplied local program once, then stores the public answer at
every ancestor. Exact product identities transfer the local retained fraction
to the root. Payload updates support persistent source-row tables.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState WeakMaps WeakMaps.WeakSystem ControllerRouting Safety PoolPalette
variable {n : ℕ}

def firstLabel (a b : Fin n) (forward : Bool) : Fin n := if forward then a else b
def secondLabel (a b : Fin n) (forward : Bool) : Fin n := if forward then b else a

theorem first_member (p : Pool n) (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (forward : Bool) : firstLabel a b forward ∈ p.members := by cases forward <;> assumption

theorem second_member (p : Pool n) (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (forward : Bool) : secondLabel a b forward ∈ p.members := by cases forward <;> assumption

theorem reverse_unknown (p : Pool n) (a b : Fin n)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true) (forward : Bool) :
    p.system.edge (secondLabel a b forward) (firstLabel a b forward) ≠ true := by
  cases forward <;> assumption

def commonChild (children : List (ℕ × Tree n)) (a b : Fin n) :
    Option {child // child ∈ children} :=
  children.attach.find? (fun child =>
    decide (a ∈ child.val.2.pool.members ∧ b ∈ child.val.2.pool.members))

theorem commonChild_members {children : List (ℕ × Tree n)} {a b : Fin n}
    {child : {child // child ∈ children}} (h : commonChild children a b = some child) :
    a ∈ child.val.2.pool.members ∧ b ∈ child.val.2.pool.members := by
  have hh := List.find?_some (p := fun child : {child // child ∈ children} =>
    decide (a ∈ child.val.2.pool.members ∧ b ∈ child.val.2.pool.members)) h
  exact of_decide_eq_true hh

theorem no_commonChild {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hn : commonChild children a b = none) :
    ¬ ∃ c, p.pins a = some c ∧ p.pins b = some c := by
  rintro ⟨c, hca, hcb⟩
  have hia : pinIndex p a = some c.val := by simp [pinIndex, hca]
  have hib : pinIndex p b = some c.val := by simp [pinIndex, hcb]
  obtain ⟨child, hc⟩ := h.covered a ha c.val hia
  have ha' := (h.members (c.val, child) hc a).mpr ⟨ha, hia⟩
  have hb' := (h.members (c.val, child) hc b).mpr ⟨hb, hib⟩
  have hn' := List.find?_eq_none.mp hn ⟨(c.val, child), hc⟩ (List.mem_attach _ _)
  exact hn' (decide_eq_true ⟨ha', hb'⟩)

theorem addComparison_bounded (p : Pool n) (a b : Fin n) (ha : a ∈ p.members)
    (hb : b ∈ p.members) (hi : Invariant (closedAdd p.system a b) p.pins)
    (h : Bounded p) : Bounded (addComparison p a b ha hb hi) := h

theorem delegatedNode_bounded
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (target : ℕ × Tree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : Tree n)
    (hold : TreeBounded (Tree.node identity p children)) (hnext : TreeBounded next) :
    TreeBounded (delegatedNode identity p children h target ht a b ha hb hba next) := by
  obtain ⟨hp, hc⟩ := (treeBounded_node_iff _ _ _).mp hold
  apply (treeBounded_node_iff _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro child hchild
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hchild
  by_cases he : old.1 = target.1
  · simpa only [if_pos he] using hnext
  · simpa only [if_neg he] using hc old hold

/-- A local program's output and its exact global-count certificate. The
executable rational charge may be below one when child births give a gain. -/
structure Answered (Payload : Type*) (t : Tree n) (a b : Fin n) where
  forward : Bool
  next : Tree n
  payload : Payload
  charge : ℚ
  wellFormed : next.WellFormed
  coherent : next.Coherent
  bounded : TreeBounded t → TreeBounded next
  members : next.pool.members = t.pool.members
  edges : next.pool.system.edge =
    (closedAdd t.pool.system (firstLabel a b forward) (secondLabel a b forward)).edge
  retention : (t.count : ℚ) ≤ charge * next.count

abbrev Stopper (Payload : Type*) (n : ℕ) :=
  ∀ (t : Tree n), t.WellFormed → t.Coherent →
    ∀ (a b : Fin n), a ∈ t.pool.members → b ∈ t.pool.members →
      t.pool.system.edge a b ≠ true → t.pool.system.edge b a ≠ true →
      (¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) → Answered Payload t a b

def routeUnknown {Payload : Type*} (stop : Stopper Payload n)
    (delegatePayload : ℕ → Fin n → Fin n → Payload → Payload)
    (t : Tree n) (h : t.WellFormed) (ho : t.Coherent)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) :
    Answered Payload t a b :=
  match t with
  | .node identity p children =>
    let hp := parts h
    match hc : commonChild children a b with
    | none => stop (.node identity p children) h ho a b ha hb hab hba
        (no_commonChild hp a b ha hb hc)
    | some child =>
      let hm := commonChild_members hc
      have hab' : child.val.2.pool.system.edge a b ≠ true := by
        rw [ho.restriction child.val child.property a hm.1 b hm.2]
        exact hab
      have hba' : child.val.2.pool.system.edge b a ≠ true := by
        rw [ho.restriction child.val child.property b hm.2 a hm.1]
        exact hba
      let result := routeUnknown stop delegatePayload child.val.2
        (hp.children_ok child.val child.property) (ho.children child.val child.property)
        a b hm.1 hm.2 hab' hba'
      let first := firstLabel a b result.forward
      let second := secondLabel a b result.forward
      let hf := first_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hs := second_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hr := reverse_unknown p a b hab hba result.forward
      let next := delegatedNode identity p children hp child.val child.property
        first second hf hs hr result.next
      { forward := result.forward
        next := next
        payload := delegatePayload identity first second result.payload
        charge := result.charge
        wellFormed := delegatedNode_wellFormed identity p children hp child.val child.property
          first second hf hs hr result.next result.wellFormed result.members
        coherent := delegatedNode_coherent identity p children hp ho child.val child.property
          first second hf hs hr result.next result.coherent result.members result.edges
        bounded := fun hbound => delegatedNode_bounded identity p children hp child.val child.property
          first second hf hs hr result.next hbound (result.bounded
            (((treeBounded_node_iff identity p children).mp hbound).2 child.val child.property))
        members := rfl
        edges := rfl
        retention := delegatedNode_retention identity p children hp child.val child.property
          first second hf hs hr result.next result.charge result.retention }
termination_by sizeOf t
decreasing_by
  have hh := List.sizeOf_lt_of_mem child.property
  rcases child with ⟨⟨key, subtree⟩, hm⟩
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at hh
  omega

theorem Answered.charge_pos {Payload : Type*} {t : Tree n} {a b : Fin n}
    (r : Answered Payload t a b) : 0 < r.charge := by
  have hp : (0 : ℚ) < t.count := by exact_mod_cast t.count_pos
  have hn : (0 : ℚ) < r.next.count := by exact_mod_cast r.next.count_pos
  exact pos_of_mul_pos_left (hp.trans_le r.retention) hn.le

end SortingAdversary.Optimal.PoolTree.Tree
