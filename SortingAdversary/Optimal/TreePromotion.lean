import SortingAdversary.Optimal.PoolTree

/-!
# Executable promotion through a parent and its actual child

An old destination receives an independent admission at the root of its
existing subtree. A new destination creates a two-position child and admits
the label there. Every old child key is transported through the parent
palette embedding; node identities are retained.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState
open WeakMaps WeakMaps.WeakSystem
open FiniteRefinement PinTransitions RefinementTransitions

variable {n : ℕ}

structure Parts (p : Pool n) (children : List (ℕ × Tree n)) : Prop where
  keys : (children.map Prod.fst).Nodup
  bounds : ∀ a ∈ children, a.1 < p.palette + 1
  occupied : ∀ a ∈ children, a.2.pool.members.Nonempty
  separated : SeparatedPins.Separated p
  children_ok : ∀ a ∈ children, a.2.WellFormed
  members : ∀ a ∈ children, ∀ x,
    x ∈ a.2.pool.members ↔ x ∈ p.members ∧ pinIndex p x = some a.1
  covered : ∀ x ∈ p.members, ∀ c, pinIndex p x = some c → ∃ t, (c, t) ∈ children

theorem parts {identity : ℕ} {p : Pool n} {children : List (ℕ × Tree n)}
    (h : (Tree.node identity p children).WellFormed) : Parts p children := by
  cases h with
  | node _ _ _ hk hb ho hs hch hm hc => exact ⟨hk, hb, ho, hs, hch, hm, hc⟩

theorem Parts.wellFormed {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (identity : ℕ) : (Tree.node identity p children).WellFormed :=
  .node identity p children h.keys h.bounds h.occupied h.separated h.children_ok h.members h.covered

theorem Parts.child_unused {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) {v : Fin n} (hv : p.pins v = none)
    (a : ℕ × Tree n) (ha : a ∈ children) : v ∉ a.2.pool.members := by
  intro hm
  have hp := ((h.members a ha v).mp hm).2
  simp [pinIndex, hv] at hp

theorem admitRoot_members (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    (t.admitRoot v hv).pool.members = insert v t.pool.members := by
  cases t with
  | node identity p children => exact (p.admission v hv).members_eq

theorem promotion_pinIndex (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) (x : Fin n) :
    pinIndex (p.installPromotion v hv c r) x =
      if x = v then some r.destination.val
      else (pinIndex p x).map (ColourTransport.extend r.embed) := by
  by_cases hx : x = v
  · subst x
    simp [pinIndex, Pool.installPromotion, Promotion.promoted_pin]
  · simp only [if_neg hx, pinIndex, Pool.installPromotion]
    rw [Promotion.other_pin p.system p.pins v c r hx]
    exact option_index_transport r.embed _

/-- A destination test uses only current colour indices. -/
def destinationExists {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) : Bool :=
  children.any (fun a => decide (ColourTransport.extend r.embed a.1 = r.destination.val))

theorem destinationExists_iff {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) :
    destinationExists r children = true ↔
      ∃ a ∈ children, ColourTransport.extend r.embed a.1 = r.destination.val := by
  simp [destinationExists]

/-- Update exactly the existing destination subtree, if it is this child. -/
def promotedChild {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) : Tree n :=
  if ColourTransport.extend r.embed a.1 = r.destination.val
    then a.2.admitRoot v (h.child_unused hv a ha) else a.2

def promotedChildren {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    List (ℕ × Tree n) :=
  children.attach.map (fun a =>
    (ColourTransport.extend r.embed a.val.1, promotedChild h v hv c r a.val a.property))

theorem promotedChildren_keys {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    (promotedChildren h v hv c r).map Prod.fst =
      (children.map Prod.fst).map (ColourTransport.extend r.embed) := by
  simp only [promotedChildren, List.map_map, Function.comp_def]
  exact List.attach_map_val (l := children) (f := fun a => ColourTransport.extend r.embed a.1)

theorem promotedChild_wellFormed {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) :
    (promotedChild h v hv c r a ha).WellFormed := by
  unfold promotedChild
  split
  · exact admitRoot_wellFormed a.2 (h.children_ok a ha) v _
  · exact h.children_ok a ha

theorem promotedChild_occupied {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) :
    (promotedChild h v hv c r a ha).pool.members.Nonempty := by
  unfold promotedChild
  split
  · rw [admitRoot_members]
    exact Finset.insert_nonempty _ _
  · exact h.occupied a ha

/-- The transformed child membership is exactly the new parent pin fibre.
This handles the admitted coordinate and every old member simultaneously. -/
theorem promotedChild_members {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) (x : Fin n) :
    x ∈ (promotedChild h v hv c r a ha).pool.members ↔
      x ∈ p.members ∧ pinIndex (p.installPromotion v hv c r) x =
        some (ColourTransport.extend r.embed a.1) := by
  have he := ColourTransport.extend_injective r.embed r.embed_strict
  rw [promotion_pinIndex]
  by_cases hs : ColourTransport.extend r.embed a.1 = r.destination.val
  · simp only [promotedChild, if_pos hs, admitRoot_members, Finset.mem_insert]
    by_cases hx : x = v
    · subst x
      simp [p.free_member hv, hs]
    · simp only [hx, false_or, if_false]
      rw [map_option_eq_some _ he]
      exact h.members a ha x
  · simp only [promotedChild, if_neg hs]
    by_cases hx : x = v
    · subst x
      simp [h.child_unused hv a ha, Ne.symm hs]
    · simp only [if_neg hx, map_option_eq_some _ he]
      exact h.members a ha x

theorem promotedChildren_contains {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) :
    (ColourTransport.extend r.embed a.1, promotedChild h v hv c r a ha) ∈
      promotedChildren h v hv c r :=
  List.mem_map.mpr ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩

/-- An older physical pin's new destination is the image of an actual old
child key; the cover condition is used, not guessed from palette membership. -/
theorem old_pin_source {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    {x : Fin n} (hx : x ≠ v) (hxm : x ∈ p.members) {key : ℕ}
    (hpin : pinIndex (p.installPromotion v hv c r) x = some key) :
    ∃ a ∈ children, ColourTransport.extend r.embed a.1 = key := by
  rw [promotion_pinIndex, if_neg hx] at hpin
  cases hp : pinIndex p x with
  | none => simp [hp] at hpin
  | some d =>
      have hd : ColourTransport.extend r.embed d = key := by simpa [hp] using hpin
      obtain ⟨child, hm⟩ := h.covered x hxm d hp
      exact ⟨(d, child), hm, hd⟩

theorem promotedChildren_covers_old {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    {x : Fin n} (hx : x ≠ v) (hxm : x ∈ p.members) {key : ℕ}
    (hpin : pinIndex (p.installPromotion v hv c r) x = some key) :
    ∃ t, (key, t) ∈ promotedChildren h v hv c r := by
  obtain ⟨a, ha, hkey⟩ := old_pin_source h v hv c r hx hxm hpin
  exact ⟨promotedChild h v hv c r a ha, hkey ▸ promotedChildren_contains h v hv c r a ha⟩

theorem promotedChildren_destination {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (hex : destinationExists r children = true) :
    ∃ t, (r.destination.val, t) ∈ promotedChildren h v hv c r := by
  obtain ⟨a, ha, hkey⟩ := (destinationExists_iff r children).mp hex
  exact ⟨promotedChild h v hv c r a ha, hkey ▸ promotedChildren_contains h v hv c r a ha⟩

/-- A newly allocated child is initialized and immediately receives its first
actual member. Its immutable identity is provided by the outer allocator. -/
def freshChild (n identity : ℕ) (v : Fin n) : Tree n :=
  (empty n identity).admitRoot v (by simp [empty, pool, emptyPool])

theorem freshChild_wellFormed (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).WellFormed :=
  admitRoot_wellFormed _ (empty_wellFormed n identity) v _

@[simp] theorem freshChild_members (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).pool.members = {v} := by
  rw [freshChild, admitRoot_members]
  rfl

@[simp] theorem freshChild_nodes (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).nodes = 1 := by
  rw [freshChild, admitRoot_nodes]
  simp [empty, nodes]

theorem freshChild_members_match {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (hn : destinationExists r children ≠ true) (identity : ℕ) (x : Fin n) :
    x ∈ (freshChild n identity v).pool.members ↔
      x ∈ p.members ∧ pinIndex (p.installPromotion v hv c r) x = some r.destination.val := by
  rw [freshChild_members, Finset.mem_singleton]
  by_cases hx : x = v
  · subst x
    simp [p.free_member hv, promotion_pinIndex]
  · constructor
    · exact fun hh => (hx hh).elim
    · rintro ⟨hxm, hpin⟩
      exact (hn ((destinationExists_iff r children).mpr
        (old_pin_source h v hv c r hx hxm hpin))).elim

/-- The actual parent/child mutation. Old children are retained and exactly
the destination child is admitted into; an absent destination is allocated. -/
def promotedNode (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) : Tree n :=
  let next := p.installPromotion v hv c r
  let oldChildren := promotedChildren h v hv c r
  if destinationExists r children = true then .node identity next oldChildren
  else .node identity next (oldChildren ++ [(r.destination.val, freshChild n freshIdentity v)])

/-- All physical child memberships and all local invariants survive the
combined parent pin and actual recursive child admission. -/
theorem promotedNode_wellFormed (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (hmate : SeparatedPins.HasMate p v) (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r freshIdentity).WellFormed := by
  let next := p.installPromotion v hv c r
  let oldChildren := promotedChildren h v hv c r
  have he := ColourTransport.extend_injective r.embed r.embed_strict
  have hkeys : (oldChildren.map Prod.fst).Nodup := by
    rw [promotedChildren_keys]
    exact h.keys.map he
  have hbounds : ∀ a ∈ oldChildren, a.1 < next.palette + 1 := by
    intro a ha
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact ColourTransport.extend_bound r.embed b.1 (h.bounds b hb)
  have hocc : ∀ a ∈ oldChildren, a.2.pool.members.Nonempty := by
    intro a ha
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact promotedChild_occupied h v hv c r b hb
  have hchild : ∀ a ∈ oldChildren, a.2.WellFormed := by
    intro a ha
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact promotedChild_wellFormed h v hv c r b hb
  have hmem : ∀ a ∈ oldChildren, ∀ x,
      x ∈ a.2.pool.members ↔ x ∈ next.members ∧ pinIndex next x = some a.1 := by
    intro a ha x
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact promotedChild_members h v hv c r b hb x
  have hsep : SeparatedPins.Separated next :=
    SeparatedPins.promotion_separated p v hv c r h.separated hmate
  by_cases hex : destinationExists r children = true
  · change WellFormed (if destinationExists r children = true then _ else _)
    rw [if_pos hex]
    refine .node identity next oldChildren hkeys hbounds hocc hsep hchild hmem ?_
    intro x hxm key hpin
    by_cases hx : x = v
    · subst x
      have hk : r.destination.val = key := by
        simpa [next, promotion_pinIndex] using hpin
      exact hk ▸ promotedChildren_destination h v hv c r hex
    · exact promotedChildren_covers_old h v hv c r hx hxm hpin
  · change WellFormed (if destinationExists r children = true then _ else _)
    rw [if_neg hex]
    have hnot : r.destination.val ∉ oldChildren.map Prod.fst := by
      rw [promotedChildren_keys]
      intro hm
      obtain ⟨key, hk, heq⟩ := List.mem_map.mp hm
      obtain ⟨a, ha, hkey⟩ := List.mem_map.mp hk
      apply hex
      exact (destinationExists_iff r children).mpr ⟨a, ha, hkey ▸ heq⟩
    refine .node identity next _ ?_ ?_ ?_ hsep ?_ ?_ ?_
    · rw [List.map_append, List.map_singleton, List.nodup_append]
      refine ⟨hkeys, by simp, ?_⟩
      intro key hk key' hd heq'
      have heq : key = r.destination.val := heq'.trans (List.mem_singleton.mp hd)
      exact hnot (heq ▸ hk)
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hbounds a ha
      · have heq := List.mem_singleton.mp ha
        subst a
        exact r.destination.isLt
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hocc a ha
      · have heq := List.mem_singleton.mp ha
        subst a
        rw [freshChild_members]
        exact Finset.singleton_nonempty v
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hchild a ha
      · have heq := List.mem_singleton.mp ha
        subst a
        exact freshChild_wellFormed n freshIdentity v
    · intro a ha x
      rcases List.mem_append.mp ha with ha | ha
      · exact hmem a ha x
      · have heq := List.mem_singleton.mp ha
        subst a
        exact freshChild_members_match h v hv c r hex freshIdentity x
    · intro x hxm key hpin
      by_cases hx : x = v
      · subst x
        have hk : r.destination.val = key := by
          simpa [next, promotion_pinIndex] using hpin
        refine ⟨freshChild n freshIdentity v, List.mem_append_right _ ?_⟩
        simp [hk]
      · obtain ⟨child, hmember⟩ := promotedChildren_covers_old h v hv c r hx hxm hpin
        exact ⟨child, List.mem_append_left _ hmember⟩

end SortingAdversary.Optimal.PoolTree.Tree
