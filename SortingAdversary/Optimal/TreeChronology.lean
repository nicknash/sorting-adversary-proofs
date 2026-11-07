import SortingAdversary.Optimal.PoolPalette
import SortingAdversary.Optimal.IncidenceLedger

/-!
# Immutable node allocation and exact promotion counts

The allocator retains all old node identities and allocates precisely the
current counter when a destination child is absent. Existing-destination
admissions do not advance the counter. These are properties of the actual
`promotedNode` operation, including its palette-key transport.
-/

namespace SortingAdversary.Optimal.TreeChronology

open PoolState PoolTree PoolTree.Tree PoolTreeAccounting PoolTreeTraversal PoolPalette

variable {n : ℕ}

def identities (t : Tree n) : List ℕ := (storedPools t).map Prod.fst

theorem identities_node (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n)) :
    identities (.node identity p children) =
      identity :: children.flatMap (fun a => identities a.2) := by
  rw [identities, storedPools]
  simp only [List.map_cons, List.map_flatMap, identities]

theorem identities_length {t : Tree n} (h : t.WellFormed) : (identities t).length = t.nodes := by
  simpa only [identities, List.length_map] using storedPools_length h

theorem admitRoot_identities (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    identities (t.admitRoot v hv) = identities t := by
  cases t with
  | node _ _ _ => simp only [admitRoot, identities_node, mapKeys, List.flatMap_map]

theorem freshChild_identities (n identity : ℕ) (v : Fin n) :
    identities (freshChild n identity v) = [identity] := by
  rw [freshChild, admitRoot_identities]
  simp [empty, identities_node]

theorem promotedChild_identities {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) :
    identities (promotedChild h v hv c r a ha) = identities a.2 := by
  unfold promotedChild
  split
  · exact admitRoot_identities _ _ _
  · rfl

theorem promotedChildren_identities {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    (promotedChildren h v hv c r).flatMap (fun a => identities a.2) =
      children.flatMap (fun a => identities a.2) := by
  simp only [promotedChildren, List.flatMap_map, promotedChild_identities]
  simpa only [List.unattach_attach] using
    (List.flatMap_subtype (l := children.attach) (g := fun a => identities a.2) (fun _ _ => rfl))

theorem promotedNode_identities (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    identities (promotedNode identity p children h v hv c r freshIdentity) =
      identities (.node identity p children) ++
        (if destinationExists r children = true then [] else [freshIdentity]) := by
  unfold promotedNode
  split
  · simp only [identities_node, promotedChildren_identities, List.append_nil]
  · simp only [identities_node, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, promotedChildren_identities, freshChild_identities, List.cons_append]

structure Allocated (t : Tree n) (nextIdentity : ℕ) : Prop where
  unique : (identities t).Nodup
  below : ∀ identity ∈ identities t, identity < nextIdentity

theorem initial_allocated (N : ℕ) : Allocated (initial N) 1 := by
  constructor <;> simp [initial, identities_node]

def nextIdentityAfter {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) (nextIdentity : ℕ) : ℕ :=
  if destinationExists r children = true then nextIdentity else nextIdentity + 1

/-- The actual allocator preserves global uniqueness at the promoted root,
and every stored identity remains below the new counter. -/
theorem promotedNode_allocated (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (nextIdentity : ℕ) (ha : Allocated (.node identity p children) nextIdentity) :
    Allocated (promotedNode identity p children h v hv c r nextIdentity)
      (nextIdentityAfter r children nextIdentity) := by
  have hid := promotedNode_identities identity p children h v hv c r nextIdentity
  by_cases hex : destinationExists r children = true
  · simp only [hex, if_true, List.append_nil] at hid
    constructor
    · simpa only [hid] using ha.unique
    · simpa only [hid, nextIdentityAfter, hex, if_true] using ha.below
  · simp only [hex] at hid
    have hfresh : nextIdentity ∉ identities (.node identity p children) :=
      fun hm => Nat.lt_irrefl _ (ha.below _ hm)
    constructor
    · rw [hid, List.nodup_append]
      refine ⟨ha.unique, by simp, ?_⟩
      intro a ha b hb hab
      have hb' : b = nextIdentity := List.mem_singleton.mp hb
      exact hfresh ((hab.trans hb') ▸ ha)
    · intro a ha'
      rw [hid] at ha'
      rw [nextIdentityAfter, if_neg hex]
      rcases List.mem_append.mp ha' with hold | hnew
      · exact (ha.below a hold).trans (Nat.lt_succ_self _)
      · have heq := List.mem_singleton.mp hnew
        subst a
        exact Nat.lt_succ_self _

theorem admitRoot_allocated (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members)
    (nextIdentity : ℕ) (h : Allocated t nextIdentity) : Allocated (t.admitRoot v hv) nextIdentity := by
  constructor
  · simpa only [admitRoot_identities] using h.unique
  · simpa only [admitRoot_identities] using h.below

theorem admitRoot_promotions (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    promotions (t.admitRoot v hv) = promotions t := by
  cases t with
  | node identity p children =>
    let a := p.admission v hv
    change promotions (.node identity a.next (mapKeys a.embed children)) =
      promotions (.node identity p children)
    rw [promotions, promotions, admission_fixed_card p v hv a]
    simp only [mapKeys, List.map_map, Function.comp_def]

theorem freshChild_promotions (n identity : ℕ) (v : Fin n) :
    promotions (freshChild n identity v) = 0 := by
  rw [freshChild, admitRoot_promotions]
  simp [empty, promotions, emptyPool, Pool.fixed]

theorem promotedChild_promotions {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) :
    promotions (promotedChild h v hv c r a ha) = promotions a.2 := by
  unfold promotedChild
  split
  · exact admitRoot_promotions _ _ _
  · rfl

theorem promotedChildren_promotions {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    ((promotedChildren h v hv c r).map (fun a => promotions a.2)).sum =
      (children.map (fun a => promotions a.2)).sum := by
  simp only [promotedChildren, List.map_map, Function.comp_def, promotedChild_promotions]
  exact congrArg List.sum (List.attach_map_val (l := children) (f := fun a => promotions a.2))

/-- A real parent promotion increments the actual tree promotion population
by exactly one. Child admissions do not double-count that event. -/
theorem promotedNode_promotions (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    promotions (promotedNode identity p children h v hv c r freshIdentity) =
      promotions (.node identity p children) + 1 := by
  unfold promotedNode
  split <;> simp only [promotions, promotion_fixed_card, promotedChildren_promotions,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, freshChild_promotions, add_zero] <;> omega

/-! ## Promotion at an arbitrary recursive node -/

/-- An explicit recursion stack with one subtree hole. Palette keys belong
to their own parent; replacing the selected subtree preserves these keys. -/
inductive Context (n : ℕ) where
  | top
  | child (identity : ℕ) (pool : Pool n) (before : List (ℕ × Tree n))
      (key : ℕ) (after : List (ℕ × Tree n)) (outer : Context n)

def Context.plug : Context n → Tree n → Tree n
  | .top, t => t
  | .child identity p before key after outer, t =>
      outer.plug (.node identity p (before ++ (key, t) :: after))

def Context.prefix : Context n → List ℕ
  | .top => []
  | .child identity _ before _ _ outer =>
      outer.prefix ++ identity :: before.flatMap (fun a => identities a.2)

def Context.suffix : Context n → List ℕ
  | .top => []
  | .child _ _ _ _ after outer =>
      after.flatMap (fun a => identities a.2) ++ outer.suffix

def Context.promotionOverhead : Context n → ℕ
  | .top => 0
  | .child _ p before _ after outer => p.fixed.card +
      (before.map (fun a => promotions a.2)).sum +
      (after.map (fun a => promotions a.2)).sum + outer.promotionOverhead

theorem Context.plug_identities (ctx : Context n) (t : Tree n) :
    identities (ctx.plug t) = ctx.prefix ++ identities t ++ ctx.suffix := by
  induction ctx generalizing t with
  | top => simp [Context.plug, Context.prefix, Context.suffix]
  | child identity p before key after outer ih =>
    rw [Context.plug, ih]
    simp only [Context.prefix, Context.suffix, identities_node, List.flatMap_append,
      List.flatMap_cons, List.append_assoc, List.cons_append]

theorem Context.plug_promotions (ctx : Context n) (t : Tree n) :
    promotions (ctx.plug t) = promotions t + ctx.promotionOverhead := by
  induction ctx generalizing t with
  | top => simp [Context.plug, Context.promotionOverhead]
  | child identity p before key after outer ih =>
    rw [Context.plug, ih, promotions]
    simp only [Context.promotionOverhead, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    omega

/-- A birth at any depth adds exactly that immutable identity to the global
identity list, up to the harmless change in its preorder position. -/
theorem Context.identities_append_perm (ctx : Context n) (t u : Tree n) (extra : List ℕ)
    (h : identities u = identities t ++ extra) :
    (identities (ctx.plug u)).Perm (identities (ctx.plug t) ++ extra) := by
  rw [ctx.plug_identities, ctx.plug_identities, h]
  have hp : (extra ++ ctx.suffix).Perm (ctx.suffix ++ extra) := List.perm_append_comm
  simpa only [List.append_assoc] using hp.append_left (ctx.prefix ++ identities t)

theorem allocated_of_perm {t u : Tree n} {nextIdentity : ℕ}
    (h : Allocated t nextIdentity) (hp : (identities u).Perm (identities t)) :
    Allocated u nextIdentity :=
  ⟨hp.nodup_iff.mpr h.unique, fun a ha => h.below a (hp.mem_iff.mp ha)⟩

theorem allocated_of_append_perm {t u : Tree n} {nextIdentity : ℕ}
    (h : Allocated t nextIdentity) (hp : (identities u).Perm (identities t ++ [nextIdentity])) :
    Allocated u (nextIdentity + 1) := by
  have hfresh : nextIdentity ∉ identities t := fun hm => Nat.lt_irrefl _ (h.below _ hm)
  constructor
  · apply hp.nodup_iff.mpr
    rw [List.nodup_append]
    refine ⟨h.unique, by simp, ?_⟩
    intro a ha b hb hab
    exact hfresh ((hab.trans (List.mem_singleton.mp hb)) ▸ ha)
  · intro a ha
    rcases List.mem_append.mp (hp.mem_iff.mp ha) with hold | hnew
    · exact (h.below a hold).trans (Nat.lt_succ_self _)
    · have heq := List.mem_singleton.mp hnew
      subst a
      exact Nat.lt_succ_self _

/-- The global allocator certificate is preserved by an actual promotion at
any node selected by an explicit recursion stack. -/
theorem Context.promotedNode_allocated (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (nextIdentity : ℕ) (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity) :
    Allocated (ctx.plug (promotedNode identity p children h v hv c r nextIdentity))
      (nextIdentityAfter r children nextIdentity) := by
  have hp := ctx.identities_append_perm (.node identity p children)
    (promotedNode identity p children h v hv c r nextIdentity) _
    (promotedNode_identities identity p children h v hv c r nextIdentity)
  by_cases hex : destinationExists r children = true
  · simp only [hex, if_true, List.append_nil] at hp
    simpa only [nextIdentityAfter, hex, if_true] using allocated_of_perm ha hp
  · simp only [hex] at hp
    simpa [nextIdentityAfter, hex] using allocated_of_append_perm ha hp

theorem Context.promotedNode_promotions (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    promotions (ctx.plug (promotedNode identity p children h v hv c r freshIdentity)) =
      promotions (ctx.plug (.node identity p children)) + 1 := by
  rw [ctx.plug_promotions, ctx.plug_promotions, TreeChronology.promotedNode_promotions]
  omega

/-- The sequential allocator has no gaps: its next counter is exactly the
number of stored nodes, in addition to bounding every immutable identity. -/
structure TightAllocated (t : Tree n) (nextIdentity : ℕ) : Prop extends Allocated t nextIdentity where
  length_eq : (identities t).length = nextIdentity

theorem initial_tightAllocated (N : ℕ) : TightAllocated (initial N) 1 := by
  refine ⟨initial_allocated N, ?_⟩
  simp [initial, identities_node]

theorem admitRoot_tightAllocated (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members)
    (nextIdentity : ℕ) (h : TightAllocated t nextIdentity) :
    TightAllocated (t.admitRoot v hv) nextIdentity := by
  refine ⟨admitRoot_allocated t v hv nextIdentity h.toAllocated, ?_⟩
  simpa only [admitRoot_identities] using h.length_eq

theorem Context.promotedNode_tightAllocated (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (nextIdentity : ℕ) (ha : TightAllocated (ctx.plug (.node identity p children)) nextIdentity) :
    TightAllocated (ctx.plug (promotedNode identity p children h v hv c r nextIdentity))
      (nextIdentityAfter r children nextIdentity) := by
  refine ⟨ctx.promotedNode_allocated identity p children h v hv c r nextIdentity ha.toAllocated, ?_⟩
  have hp := ctx.identities_append_perm (.node identity p children)
    (promotedNode identity p children h v hv c r nextIdentity) _
    (promotedNode_identities identity p children h v hv c r nextIdentity)
  have hlength := hp.length_eq
  rw [List.length_append, ha.length_eq] at hlength
  by_cases hex : destinationExists r children = true <;>
    simpa [nextIdentityAfter, hex] using hlength

/-- Therefore immutable-ID tables indexed below the allocator counter need
at most `2s-1` entries for a subtree whose root has `s` actual members. -/
theorem counter_add_one_le_twice_members {t : Tree n} {nextIdentity : ℕ}
    (ha : TightAllocated t nextIdentity) (h : t.WellFormed) (hn : t.pool.members.Nonempty) :
    nextIdentity + 1 ≤ 2 * t.pool.members.card := by
  rw [← ha.length_eq, identities_length h]
  exact nodes_add_one_le_twice_members h hn

end SortingAdversary.Optimal.TreeChronology
