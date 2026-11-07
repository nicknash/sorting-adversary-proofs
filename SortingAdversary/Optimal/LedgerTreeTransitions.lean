import SortingAdversary.Optimal.LedgerTreeBridge
import SortingAdversary.Optimal.TreeReplacement

/-!
# Actual tree transitions preserve the chronological ledger

Locations use immutable node identities. A parent promotion performs exactly
one ledger promotion and one admission into the computed destination child.
The source endpoint required by the ledger is an actual earlier physical
comparison; public comparability alone is deliberately insufficient.
-/

namespace SortingAdversary.Optimal.LedgerTreeTransitions

open PoolState PoolTree PoolTree.Tree PoolTreeTraversal TreeChronology LedgerTreeBridge

variable {n : ℕ}

def rootIdentity : Tree n → ℕ
  | .node identity _ _ => identity

theorem root_mem_storedPools (t : Tree n) :
    (rootIdentity t, t.pool) ∈ storedPools t := by
  cases t
  simp only [rootIdentity, pool, storedPools, List.mem_cons_self]

def forestLocations (children : List (ℕ × Tree n))
    (select : Pool n → Finset (Fin n)) : Finset (IncidenceLedger.Location n) :=
  children.foldr (fun a rest => treeLocations a.2 select ∪ rest) ∅

theorem mem_forestLocations (children : List (ℕ × Tree n))
    (select : Pool n → Finset (Fin n)) (location : IncidenceLedger.Location n) :
    location ∈ forestLocations children select ↔
      ∃ a ∈ children, location ∈ treeLocations a.2 select := by
  induction children with
  | nil => simp [forestLocations]
  | cons a rest ih =>
    change location ∈ treeLocations a.2 select ∪ forestLocations rest select ↔ _
    simp only [Finset.mem_union, ih, List.mem_cons, or_and_right, exists_or, exists_eq_left]

theorem treeLocations_node (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (select : Pool n → Finset (Fin n)) :
    treeLocations (.node identity p children) select =
      nodeLocations identity (select p) ∪ forestLocations children select := by
  ext location
  simp only [mem_treeLocations, storedPools, List.mem_cons, List.mem_flatMap,
    Finset.mem_union, mem_nodeLocations, mem_forestLocations]
  constructor
  · rintro ⟨a, rfl | ⟨child, hc, ha⟩, hi, hx⟩
    · exact Or.inl ⟨hi, hx⟩
    · exact Or.inr ⟨child, hc, a, ha, hi, hx⟩
  · rintro (⟨hi, hx⟩ | ⟨child, hc, a, ha, hi, hx⟩)
    · exact ⟨(identity, p), Or.inl rfl, hi, hx⟩
    · exact ⟨a, Or.inr ⟨child, hc, ha⟩, hi, hx⟩

theorem forestLocations_mapKeys {K L : ℕ} (embed : Fin K → Fin L)
    (children : List (ℕ × Tree n)) (select : Pool n → Finset (Fin n)) :
    forestLocations (mapKeys embed children) select = forestLocations children select := by
  induction children with
  | nil => rfl
  | cons a rest ih =>
    simpa only [mapKeys, List.map_cons, forestLocations, List.foldr_cons] using
      (congrArg (fun s => treeLocations a.2 select ∪ s) ih)

theorem treeLocations_admitRoot (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members)
    (select : Pool n → Finset (Fin n))
    (hadmit : select (t.pool.admission v hv).next = insert v (select t.pool)) :
    treeLocations (t.admitRoot v hv) select =
      insert (rootIdentity t, v) (treeLocations t select) := by
  cases t with
  | node identity p children =>
    change select (p.admission v hv).next = insert v (select p) at hadmit
    simp only [admitRoot, treeLocations_node, forestLocations_mapKeys, hadmit,
      nodeLocations, Finset.image_insert, Finset.insert_union, rootIdentity]

theorem enteredLocations_admitRoot (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    enteredLocations (t.admitRoot v hv) = insert (rootIdentity t, v) (enteredLocations t) :=
  treeLocations_admitRoot t v hv Pool.members (t.pool.admission v hv).members_eq

theorem freeLocations_admitRoot (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    freeLocations (t.admitRoot v hv) = insert (rootIdentity t, v) (freeLocations t) :=
  treeLocations_admitRoot t v hv Pool.free (Pool.Admission.free_eq _ _ _)

theorem treeLocations_at_identity {t : Tree n} {nextIdentity : ℕ}
    (ha : Allocated t nextIdentity) (a : ℕ × Pool n) (ha_mem : a ∈ storedPools t)
    (select : Pool n → Finset (Fin n)) (x : Fin n) :
    (a.1, x) ∈ treeLocations t select ↔ x ∈ select a.2 := by
  constructor
  · intro hx
    obtain ⟨b, hb, hid, hbx⟩ := (mem_treeLocations _ _ _).mp hx
    have heq : a = b := List.inj_on_of_nodup_map ha.unique ha_mem hb hid
    exact heq.symm ▸ hbx
  · intro hx
    exact (mem_treeLocations _ _ _).mpr ⟨a, ha_mem, rfl, hx⟩

theorem location_identity_mem {t : Tree n} (select : Pool n → Finset (Fin n))
    {location : IncidenceLedger.Location n} (h : location ∈ treeLocations t select) :
    location.1 ∈ identities t := by
  obtain ⟨a, ha, hid, _⟩ := (mem_treeLocations _ _ _).mp h
  exact List.mem_map.mpr ⟨a, ha, hid.symm⟩

/-- The actual old destination, found by scanning current palette keys. -/
def destinationChild {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) :
    Option (ℕ × Tree n) :=
  children.find? (fun a => decide (ColourTransport.extend r.embed a.1 = r.destination.val))

/-- The immutable receiving identity, using the allocator only on a birth. -/
def receivingIdentity {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n))
    (freshIdentity : ℕ) : ℕ :=
  match destinationChild r children with
  | some a => rootIdentity a.2
  | none => freshIdentity

theorem destinationChild_some {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n))
    {a : ℕ × Tree n} (h : destinationChild r children = some a) :
    a ∈ children ∧ ColourTransport.extend r.embed a.1 = r.destination.val := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  exact of_decide_eq_true (List.find?_some
    (p := fun a : ℕ × Tree n => decide (ColourTransport.extend r.embed a.1 = r.destination.val)) h)

theorem destinationChild_none_iff {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) :
    destinationChild r children = none ↔ destinationExists r children ≠ true := by
  simp [destinationChild, destinationExists]

theorem destinationChild_eq_some {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (a : ℕ × Tree n) (ha : a ∈ children)
    (hkey : ColourTransport.extend r.embed a.1 = r.destination.val) :
    destinationChild r children = some a := by
  cases hd : destinationChild r children with
  | none =>
    exact False.elim ((destinationChild_none_iff r children).mp hd
      ((destinationExists_iff r children).mpr ⟨a, ha, hkey⟩))
  | some b =>
    obtain ⟨hb, hbkey⟩ := destinationChild_some r children hd
    have heq : a = b := h.unique_key ha hb
      ((ColourTransport.extend_injective r.embed r.embed_strict) (hkey.trans hbkey.symm))
    exact congrArg some heq.symm

theorem mem_promotedChildren_locations {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (select : Pool n → Finset (Fin n))
    (hadmit : ∀ (q : Pool n) (x : Fin n) (hx : x ∉ q.members),
      select (q.admission x hx).next = insert x (select q))
    (location : IncidenceLedger.Location n) :
    location ∈ forestLocations (promotedChildren h v hv c r) select ↔
      location ∈ forestLocations children select ∨
        ∃ a ∈ children, ColourTransport.extend r.embed a.1 = r.destination.val ∧
          location = (rootIdentity a.2, v) := by
  constructor
  · intro hl
    obtain ⟨b, hb, hlb⟩ := (mem_forestLocations _ _ _).mp hl
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := List.mem_map.mp hb
    change location ∈ treeLocations (promotedChild h v hv c r a ha) select at hlb
    by_cases hkey : ColourTransport.extend r.embed a.1 = r.destination.val
    · rw [promotedChild, if_pos hkey, treeLocations_admitRoot _ _ _ select (hadmit _ _ _)] at hlb
      rcases Finset.mem_insert.mp hlb with heq | hold
      · exact Or.inr ⟨a, ha, hkey, heq⟩
      · exact Or.inl ((mem_forestLocations _ _ _).mpr ⟨a, ha, hold⟩)
    · rw [promotedChild, if_neg hkey] at hlb
      exact Or.inl ((mem_forestLocations _ _ _).mpr ⟨a, ha, hlb⟩)
  · rintro (hold | ⟨a, ha, hkey, rfl⟩)
    · obtain ⟨a, ha, hla⟩ := (mem_forestLocations _ _ _).mp hold
      refine (mem_forestLocations _ _ _).mpr
        ⟨(ColourTransport.extend r.embed a.1, promotedChild h v hv c r a ha),
          List.mem_map.mpr ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩, ?_⟩
      change location ∈ treeLocations (promotedChild h v hv c r a ha) select
      by_cases hkey : ColourTransport.extend r.embed a.1 = r.destination.val
      · rw [promotedChild, if_pos hkey, treeLocations_admitRoot _ _ _ select (hadmit _ _ _)]
        exact Finset.mem_insert_of_mem hla
      · simpa only [promotedChild, if_neg hkey] using hla
    · refine (mem_forestLocations _ _ _).mpr
        ⟨(ColourTransport.extend r.embed a.1, promotedChild h v hv c r a ha),
          List.mem_map.mpr ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩, ?_⟩
      change (rootIdentity a.2, v) ∈ treeLocations (promotedChild h v hv c r a ha) select
      rw [promotedChild, if_pos hkey, treeLocations_admitRoot _ _ _ select (hadmit _ _ _)]
      exact Finset.mem_insert_self _ _

theorem forestLocations_promotedChildren {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) (select : Pool n → Finset (Fin n))
    (hadmit : ∀ (q : Pool n) (x : Fin n) (hx : x ∉ q.members),
      select (q.admission x hx).next = insert x (select q)) :
    forestLocations (promotedChildren h v hv c r) select =
      if destinationExists r children then
        insert (receivingIdentity r children freshIdentity, v) (forestLocations children select)
      else forestLocations children select := by
  cases hd : destinationChild r children with
  | none =>
    have hex := (destinationChild_none_iff r children).mp hd
    rw [if_neg hex]
    ext location
    rw [mem_promotedChildren_locations h v hv c r select hadmit]
    constructor
    · rintro (hold | ⟨a, ha, hkey, _⟩)
      · exact hold
      · exact False.elim (hex ((destinationExists_iff r children).mpr ⟨a, ha, hkey⟩))
    · exact Or.inl
  | some a =>
    obtain ⟨ha, hkey⟩ := destinationChild_some r children hd
    have hex := (destinationExists_iff r children).mpr ⟨a, ha, hkey⟩
    rw [if_pos hex]
    simp only [receivingIdentity, hd]
    ext location
    rw [mem_promotedChildren_locations h v hv c r select hadmit, Finset.mem_insert]
    constructor
    · rintro (hold | ⟨b, hb, hbkey, hloc⟩)
      · exact Or.inr hold
      · have hba : b = a := h.unique_key hb ha
          ((ColourTransport.extend_injective r.embed r.embed_strict) (hbkey.trans hkey.symm))
        exact Or.inl (hba ▸ hloc)
    · rintro (rfl | hold)
      · exact Or.inr ⟨a, ha, hkey, rfl⟩
      · exact Or.inl hold

theorem forestLocations_append (before after : List (ℕ × Tree n))
    (select : Pool n → Finset (Fin n)) :
    forestLocations (before ++ after) select =
      forestLocations before select ∪ forestLocations after select := by
  ext location
  simp only [mem_forestLocations, List.mem_append, Finset.mem_union, or_and_right, exists_or]

theorem treeLocations_freshChild (identity : ℕ) (v : Fin n)
    (select : Pool n → Finset (Fin n))
    (hadmit : ∀ (q : Pool n) (x : Fin n) (hx : x ∉ q.members),
      select (q.admission x hx).next = insert x (select q))
    (hempty : select (emptyPool n) = ∅) :
    treeLocations (freshChild n identity v) select = {(identity, v)} := by
  rw [freshChild, treeLocations_admitRoot _ _ _ select (hadmit _ _ _)]
  simp only [empty, rootIdentity, treeLocations_node, hempty, nodeLocations, Finset.image_empty,
    forestLocations, List.foldr_nil, Finset.union_empty]
  rfl

theorem treeLocations_promotedNode (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ)
    (select : Pool n → Finset (Fin n))
    (hadmit : ∀ (q : Pool n) (x : Fin n) (hx : x ∉ q.members),
      select (q.admission x hx).next = insert x (select q))
    (hempty : select (emptyPool n) = ∅) :
    treeLocations (promotedNode identity p children h v hv c r freshIdentity) select =
      insert (receivingIdentity r children freshIdentity, v)
        (nodeLocations identity (select (p.installPromotion v hv c r)) ∪
          forestLocations children select) := by
  unfold promotedNode
  split
  next hex =>
    rw [treeLocations_node, forestLocations_promotedChildren h v hv c r freshIdentity select hadmit,
      if_pos hex, Finset.union_insert]
  next hex =>
    have hd := (destinationChild_none_iff r children).mpr hex
    rw [treeLocations_node, forestLocations_append,
      forestLocations_promotedChildren h v hv c r freshIdentity select hadmit, if_neg hex]
    have hf : forestLocations [(r.destination.val, freshChild n freshIdentity v)] select =
        {(freshIdentity, v)} := by
      change treeLocations (freshChild n freshIdentity v) select ∪ ∅ = _
      rw [treeLocations_freshChild _ _ select hadmit hempty, Finset.union_empty]
    rw [hf]
    simp only [receivingIdentity, hd]
    ext location
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto

def outsideLocations (ctx : Context n) (select : Pool n → Finset (Fin n)) :
    Finset (IncidenceLedger.Location n) :=
  match ctx with
  | .top => ∅
  | .child identity p before _ after outer =>
      nodeLocations identity (select p) ∪ forestLocations before select ∪
        forestLocations after select ∪ outsideLocations outer select

theorem treeLocations_plug (ctx : Context n) (t : Tree n)
    (select : Pool n → Finset (Fin n)) :
    treeLocations (ctx.plug t) select = treeLocations t select ∪ outsideLocations ctx select := by
  induction ctx generalizing t with
  | top => simp [Context.plug, outsideLocations]
  | child identity p before key after outer ih =>
    rw [Context.plug, ih, treeLocations_node, forestLocations_append]
    change _ = _ ∪ (nodeLocations identity (select p) ∪ forestLocations before select ∪
      forestLocations after select ∪ outsideLocations outer select)
    simp only [forestLocations, List.foldr_cons]
    ac_rfl

theorem storedPools_mem_plug (ctx : Context n) {t : Tree n} {a : ℕ × Pool n}
    (ha : a ∈ storedPools t) : a ∈ storedPools (ctx.plug t) := by
  induction ctx generalizing t with
  | top => exact ha
  | child identity p before key after outer ih =>
    apply ih
    rw [storedPools]
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨(key, t), by simp, ha⟩

theorem promotedNode_pool (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r freshIdentity).pool =
      p.installPromotion v hv c r := by
  unfold promotedNode
  split <;> rfl

theorem promotedNode_rootIdentity (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    rootIdentity (promotedNode identity p children h v hv c r freshIdentity) = identity := by
  unfold promotedNode
  split <;> rfl

theorem enteredLocations_promotedNode (ctx : Context n) (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    enteredLocations (ctx.plug (promotedNode identity p children h v hv c r freshIdentity)) =
      insert (receivingIdentity r children freshIdentity, v)
        (enteredLocations (ctx.plug (.node identity p children))) := by
  rw [enteredLocations, treeLocations_plug,
    treeLocations_promotedNode identity p children h v hv c r freshIdentity Pool.members
      (fun q x hx => (q.admission x hx).members_eq) rfl,
    Finset.insert_union]
  change insert _ (nodeLocations identity p.members ∪ forestLocations children Pool.members ∪
    outsideLocations ctx Pool.members) = _
  rw [enteredLocations, treeLocations_plug, treeLocations_node]

theorem receivingLocation_not_entered (ctx : Context n) (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (nextIdentity : ℕ)
    (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity) :
    (receivingIdentity r children nextIdentity, v) ∉
      enteredLocations (ctx.plug (.node identity p children)) := by
  cases hd : destinationChild r children with
  | none =>
    simp only [receivingIdentity, hd]
    intro hl
    exact Nat.lt_irrefl _ (ha.below _ (location_identity_mem Pool.members hl))
  | some a =>
    obtain ⟨hamem, _⟩ := destinationChild_some r children hd
    simp only [receivingIdentity, hd]
    have hroot : (rootIdentity a.2, a.2.pool) ∈
        storedPools (ctx.plug (.node identity p children)) := by
      apply storedPools_mem_plug ctx
      rw [storedPools]
      exact List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨a, hamem, root_mem_storedPools a.2⟩)
    exact fun hl => h.child_unused hv a hamem
      ((treeLocations_at_identity ha _ hroot Pool.members v).mp hl)

theorem nodeLocations_erase (identity : ℕ) (labels : Finset (Fin n)) (v : Fin n) :
    nodeLocations identity (labels.erase v) = (nodeLocations identity labels).erase (identity, v) := by
  ext ⟨i, x⟩
  simp only [mem_nodeLocations, Finset.mem_erase, ne_eq, Prod.mk.injEq]
  tauto

theorem promotedLocation_not_free (ctx : Context n) (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (nextIdentity : ℕ)
    (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity) :
    (identity, v) ∉
      freeLocations (ctx.plug (promotedNode identity p children h v hv c r nextIdentity)) := by
  have ha' := ctx.promotedNode_allocated identity p children h v hv c r nextIdentity ha
  have hroot : (identity, p.installPromotion v hv c r) ∈
      storedPools (ctx.plug (promotedNode identity p children h v hv c r nextIdentity)) := by
    apply storedPools_mem_plug ctx
    simpa only [promotedNode_rootIdentity, promotedNode_pool] using
      root_mem_storedPools (promotedNode identity p children h v hv c r nextIdentity)
  intro hl
  have hv' := (treeLocations_at_identity ha' _ hroot Pool.free v).mp hl
  rw [Pool.installPromotion_free] at hv'
  exact Finset.notMem_erase _ _ hv'

theorem freeLocations_promotedNode (ctx : Context n) (identity : ℕ) (p : Pool n)
    (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (nextIdentity : ℕ)
    (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity) :
    freeLocations (ctx.plug (promotedNode identity p children h v hv c r nextIdentity)) =
      insert (receivingIdentity r children nextIdentity, v)
        ((freeLocations (ctx.plug (.node identity p children))).erase (identity, v)) := by
  have hf : freeLocations (ctx.plug (promotedNode identity p children h v hv c r nextIdentity)) =
      insert (receivingIdentity r children nextIdentity, v)
        ((nodeLocations identity p.free).erase (identity, v) ∪
          forestLocations children Pool.free ∪ outsideLocations ctx Pool.free) := by
    rw [freeLocations, treeLocations_plug,
      treeLocations_promotedNode identity p children h v hv c r nextIdentity Pool.free
        (fun q x hx => Pool.Admission.free_eq q x (q.admission x hx)) (emptyPool_free n),
      Pool.installPromotion_free, nodeLocations_erase, Finset.insert_union]
  have hnot := promotedLocation_not_free ctx identity p children h v hv c r nextIdentity ha
  rw [hf] at hnot
  have hforest : (identity, v) ∉ forestLocations children Pool.free := by
    intro hm
    exact hnot (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have houtside : (identity, v) ∉ outsideLocations ctx Pool.free := by
    intro hm
    exact hnot (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm))
  rw [hf, freeLocations, treeLocations_plug, treeLocations_node]
  congr 1
  ext location
  by_cases he : location = (identity, v)
  · subst location
    simp [hforest, houtside]
  · simp only [Finset.mem_union, Finset.mem_erase, ne_eq, he, not_false_eq_true, true_and]

def promotionActions (identity : ℕ) (v : Fin n) (kind : IncidenceLedger.Kind)
    {p : Pool n} {c : Fin (p.palette + 1)} (r : Promotion.Result p.system p.pins v c)
    (children : List (ℕ × Tree n)) (nextIdentity : ℕ) : List (IncidenceLedger.Action n) :=
  [.promote (identity, v) kind, .admit (receivingIdentity r children nextIdentity, v)]

/-- The concrete ledger record produced by the two actual tree events. -/
def promotionLedger (s : IncidenceLedger.State n) (identity : ℕ) (v : Fin n)
    (kind : IncidenceLedger.Kind) {p : Pool n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n))
    (nextIdentity : ℕ) : IncidenceLedger.State n :=
  { s with
    entered := insert (receivingIdentity r children nextIdentity, v) s.entered
    free := insert (receivingIdentity r children nextIdentity, v) (s.free.erase (identity, v))
    moves := insert ⟨(identity, v), kind, IncidenceLedger.incidences s.calls (identity, v)⟩ s.moves }

/-- Acceptance follows from actual membership, the fresh receiving location,
and a recorded old endpoint. No numerical promotion budget is a premise. -/
theorem run_promotionActions (threshold : ℕ) (s : IncidenceLedger.State n)
    (ctx : Context n) (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (nextIdentity : ℕ) (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity)
    (hrep : Represents s (ctx.plug (.node identity p children)))
    (kind : IncidenceLedger.Kind) (witness : IncidenceLedger.Endpoint)
    (hrecorded : witness ∈ IncidenceLedger.incidences s.calls (identity, v))
    (hdegree : kind = .degree → threshold ≤ IncidenceLedger.liveDegree s (identity, v)) :
    IncidenceLedger.run threshold s (promotionActions identity v kind r children nextIdentity) =
      some (promotionLedger s identity v kind r children nextIdentity) := by
  have hfree : (identity, v) ∈ s.free := by
    rw [hrep.free]
    apply (mem_treeLocations _ _ _).mpr
    refine ⟨(identity, p), storedPools_mem_plug ctx (by simp [storedPools]), rfl, ?_⟩
    exact (p.free_iff v).mpr hv
  have hnew : (receivingIdentity r children nextIdentity, v) ∉ s.entered := by
    rw [hrep.entered]
    exact receivingLocation_not_entered ctx identity p children h v hv c r nextIdentity ha
  have hcheck : (identity, v) ∈ s.free ∧
      (IncidenceLedger.incidences s.calls (identity, v)).Nonempty ∧
      (kind = .degree → threshold ≤ IncidenceLedger.liveDegree s (identity, v)) :=
    ⟨hfree, ⟨witness, hrecorded⟩, hdegree⟩
  simp only [promotionActions, IncidenceLedger.run, IncidenceLedger.step, if_pos hcheck,
    Option.bind_some, if_pos hnew, promotionLedger]

theorem promotionLedger_represents (s : IncidenceLedger.State n)
    (ctx : Context n) (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (nextIdentity : ℕ) (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity)
    (hrep : Represents s (ctx.plug (.node identity p children))) (kind : IncidenceLedger.Kind) :
    Represents (promotionLedger s identity v kind r children nextIdentity)
      (ctx.plug (promotedNode identity p children h v hv c r nextIdentity)) := by
  constructor
  · change insert _ s.entered = _
    rw [hrep.entered, enteredLocations_promotedNode]
  · change insert _ (s.free.erase (identity, v)) = _
    rw [hrep.free, freeLocations_promotedNode ctx identity p children h v hv c r nextIdentity ha]

theorem treeLocations_poolUpdate (ctx : Context n) (identity : ℕ) (p q : Pool n)
    (children : List (ℕ × Tree n)) (select : Pool n → Finset (Fin n))
    (hq : select q = select p) :
    treeLocations (ctx.plug (.node identity q children)) select =
      treeLocations (ctx.plug (.node identity p children)) select := by
  rw [treeLocations_plug, treeLocations_plug, treeLocations_node, treeLocations_node, hq]

/-- Changing primitive walls or the stored public order preserves the ledger
whenever the actual member and physical-pin sets stay unchanged. -/
theorem represents_poolUpdate (s : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (p q : Pool n) (children : List (ℕ × Tree n))
    (hm : q.members = p.members) (hf : q.free = p.free)
    (hrep : Represents s (ctx.plug (.node identity p children))) :
    Represents s (ctx.plug (.node identity q children)) := by
  constructor
  · exact hrep.entered.trans (treeLocations_poolUpdate ctx identity p q children Pool.members hm).symm
  · exact hrep.free.trans (treeLocations_poolUpdate ctx identity p q children Pool.free hf).symm

theorem represents_stopNode (s : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : ControllerRouting.Invariant (Safety.closedAdd p.system a b) p.pins)
    (hrep : Represents s (ctx.plug (.node identity p children))) :
    Represents s (ctx.plug (stopNode identity p children a b ha hb hi)) :=
  represents_poolUpdate s ctx identity p (addComparison p a b ha hb hi) children rfl rfl hrep

def physicalLedger (s : IncidenceLedger.State n) (row : Option (IncidenceLedger.Row n)) :
    IncidenceLedger.State n := { s with calls := s.calls ++ [row] }

theorem step_physicalLedger (threshold : ℕ) (s : IncidenceLedger.State n)
    (row : Option (IncidenceLedger.Row n)) (hrow : IncidenceLedger.rowAdmissible s row) :
    IncidenceLedger.step threshold s (.physical row) = some (physicalLedger s row) := by
  simp only [IncidenceLedger.step, if_pos hrow, physicalLedger]

theorem physicalLedger_represents (s : IncidenceLedger.State n) (t : Tree n)
    (row : Option (IncidenceLedger.Row n)) (hrep : Represents s t) :
    Represents (physicalLedger s row) t := ⟨hrep.entered, hrep.free⟩

theorem realRow_admissible (s : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (a b : Fin n) (ha : p.pins a = none) (hb : p.pins b = none) (hab : a ≠ b)
    (hrep : Represents s (ctx.plug (.node identity p children))) :
    IncidenceLedger.rowAdmissible s (some ⟨identity, a, b⟩) := by
  have hroot : (identity, p) ∈ storedPools (ctx.plug (.node identity p children)) :=
    storedPools_mem_plug ctx (by simp [storedPools])
  refine ⟨?_, ?_, hab⟩
  · change (identity, a) ∈ s.free
    rw [hrep.free]
    exact (mem_treeLocations _ _ _).mpr ⟨(identity, p), hroot, rfl, (p.free_iff a).mpr ha⟩
  · change (identity, b) ∈ s.free
    rw [hrep.free]
    exact (mem_treeLocations _ _ _).mpr ⟨(identity, p), hroot, rfl, (p.free_iff b).mpr hb⟩

/-- Every physical call advances one common clock, while a real free--free
call records its two original endpoints at the actual stopping node. -/
theorem physicalLedger_call_count (s : IncidenceLedger.State n)
    (row : Option (IncidenceLedger.Row n)) :
    (physicalLedger s row).calls.length = s.calls.length + 1 := by
  simp [physicalLedger]

end SortingAdversary.Optimal.LedgerTreeTransitions
