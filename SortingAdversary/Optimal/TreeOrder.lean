import SortingAdversary.Optimal.TreePromotion

/-!
# Public-order coherence throughout the actual pool tree

Each child records exactly the restriction of its parent's public order to
its members. Births preserve this equality because the promoted coordinate
is incomparable with every old member of its destination. Numerical weak
maps and physical public orders remain separate throughout this argument.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState WeakMaps WeakMaps.WeakSystem

variable {n : ℕ}

inductive Coherent : Tree n → Prop where
  | node (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
      (children_ok : ∀ a ∈ children, Coherent a.2)
      (restriction : ∀ a ∈ children, ∀ x ∈ a.2.pool.members,
        ∀ y ∈ a.2.pool.members, a.2.pool.system.edge x y = p.system.edge x y) :
      Coherent (.node identity p children)

theorem Coherent.children {identity : ℕ} {p : Pool n} {children : List (ℕ × Tree n)}
    (h : (Tree.node identity p children).Coherent) : ∀ a ∈ children, a.2.Coherent := by
  cases h with | node _ _ _ hc _ => exact hc

theorem Coherent.restriction {identity : ℕ} {p : Pool n} {children : List (ℕ × Tree n)}
    (h : (Tree.node identity p children).Coherent) :
    ∀ a ∈ children, ∀ x ∈ a.2.pool.members, ∀ y ∈ a.2.pool.members,
      a.2.pool.system.edge x y = p.system.edge x y := by
  cases h with | node _ _ _ _ hr => exact hr

theorem initial_coherent (N : ℕ) : (initial N).Coherent :=
  .node _ _ _ (by simp) (by simp)

theorem empty_coherent (n identity : ℕ) : (empty n identity).Coherent :=
  .node _ _ _ (by simp) (by simp)

theorem admitRoot_edges (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members) :
    (t.admitRoot v hv).pool.system.edge = t.pool.system.edge := by
  cases t with | node _ p _ => exact (p.admission v hv).edges

theorem admitRoot_coherent (t : Tree n) (h : t.Coherent)
    (v : Fin n) (hv : v ∉ t.pool.members) : (t.admitRoot v hv).Coherent := by
  cases t with
  | node identity p children =>
    let a := p.admission v hv
    change (Tree.node identity a.next (mapKeys a.embed children)).Coherent
    refine .node _ _ _ ?_ ?_
    · intro b hb
      obtain ⟨old, hold, heq⟩ := List.mem_map.mp
        (show b ∈ children.map (fun c => (ColourTransport.extend a.embed c.1, c.2)) from hb)
      subst b
      exact h.children old hold
    · intro b hb x hx y hy
      obtain ⟨old, hold, heq⟩ := List.mem_map.mp
        (show b ∈ children.map (fun c => (ColourTransport.extend a.embed c.1, c.2)) from hb)
      subst b
      rw [a.edges]
      exact h.restriction old hold x hx y hy

theorem freshChild_coherent (n identity : ℕ) (v : Fin n) :
    (freshChild n identity v).Coherent :=
  admitRoot_coherent _ (empty_coherent n identity) v _

theorem Parts.pin_witness {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (a : ℕ × Tree n) (ha : a ∈ children)
    (x : Fin n) (hx : x ∈ a.2.pool.members) :
    ∃ d, p.pins x = some d ∧ d.val = a.1 := by
  have hp := ((h.members a ha x).mp hx).2
  unfold pinIndex at hp
  cases hd : p.pins x with
  | none => simp [hd] at hp
  | some d => exact ⟨d, rfl, by simpa [hd] using hp⟩

theorem destination_independent {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children)
    (hs : ColourTransport.extend r.embed a.1 = r.destination.val)
    (x : Fin n) (hx : x ∈ a.2.pool.members) :
    p.system.edge x v = false ∧ p.system.edge v x = false := by
  obtain ⟨d, hd, hkey⟩ := h.pin_witness a ha x hx
  have he : r.embed d = r.destination := by
    apply Fin.ext
    simpa only [← hkey, ColourTransport.extend_at] using hs
  have hi := r.independent x d hd he
  exact ⟨Bool.eq_false_iff.mpr hi.1, Bool.eq_false_iff.mpr hi.2⟩

theorem unused_edges (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (x : Fin n) (hx : x ∈ p.members) :
    p.system.edge v x = false ∧ p.system.edge x v = false := by
  have hne : x ≠ v := fun he => hv (he ▸ hx)
  have hu := (p.outside v hv).2
  exact ⟨Bool.eq_false_iff.mpr (fun he => hne (hu.outgoing x he)),
    Bool.eq_false_iff.mpr (fun he => hne (hu.incoming x he))⟩

theorem promotedChild_coherent {identity : ℕ} {p : Pool n}
    {children : List (ℕ × Tree n)} (h : Parts p children)
    (ho : (Tree.node identity p children).Coherent)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (a : ℕ × Tree n) (ha : a ∈ children) :
    (promotedChild h v hv c r a ha).Coherent := by
  unfold promotedChild
  split
  · exact admitRoot_coherent _ (ho.children a ha) v _
  · exact ho.children a ha

theorem promotedChild_restriction {identity : ℕ} {p : Pool n}
    {children : List (ℕ × Tree n)} (h : Parts p children)
    (ho : (Tree.node identity p children).Coherent)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (a : ℕ × Tree n) (ha : a ∈ children)
    (x : Fin n) (hx : x ∈ (promotedChild h v hv c r a ha).pool.members)
    (y : Fin n) (hy : y ∈ (promotedChild h v hv c r a ha).pool.members) :
    (promotedChild h v hv c r a ha).pool.system.edge x y = r.system.edge x y := by
  by_cases hs : ColourTransport.extend r.embed a.1 = r.destination.val
  · have ht : promotedChild h v hv c r a ha =
        a.2.admitRoot v (h.child_unused hv a ha) := if_pos hs
    rw [ht] at hx hy ⊢
    rw [admitRoot_edges, r.edges]
    rw [admitRoot_members] at hx hy
    rcases Finset.mem_insert.mp hx with hxx | hxm
    · subst x
      rcases Finset.mem_insert.mp hy with hyy | hym
      · subst y
        rw [a.2.pool.invariant.closed.refl, p.invariant.closed.refl]
      · rw [(unused_edges _ _ (h.child_unused hv a ha) y hym).1,
          (destination_independent h v c r a ha hs y hym).2]
    · rcases Finset.mem_insert.mp hy with hyy | hym
      · subst y
        rw [(unused_edges _ _ (h.child_unused hv a ha) x hxm).2,
          (destination_independent h v c r a ha hs x hxm).1]
      · exact ho.restriction a ha x hxm y hym
  · have ht : promotedChild h v hv c r a ha = a.2 := if_neg hs
    rw [ht] at hx hy ⊢
    rw [r.edges]
    exact ho.restriction a ha x hx y hy

theorem promotedNode_coherent (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (ho : (Tree.node identity p children).Coherent)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (freshIdentity : ℕ) :
    (promotedNode identity p children h v hv c r freshIdentity).Coherent := by
  have hc : ∀ a ∈ promotedChildren h v hv c r, a.2.Coherent := by
    intro a ha
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact promotedChild_coherent h ho v hv c r b hb
  have hr : ∀ a ∈ promotedChildren h v hv c r,
      ∀ x ∈ a.2.pool.members, ∀ y ∈ a.2.pool.members,
      a.2.pool.system.edge x y = r.system.edge x y := by
    intro a ha x hx y hy
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact promotedChild_restriction h ho v hv c r b hb x hx y hy
  unfold promotedNode
  split
  · exact .node _ _ _ hc hr
  · refine .node _ _ _ ?_ ?_
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hc a ha
      · have he := List.mem_singleton.mp ha
        subst a
        exact freshChild_coherent n freshIdentity v
    · intro a ha x hx y hy
      rcases List.mem_append.mp ha with ha | ha
      · exact hr a ha x hx y hy
      · have he := List.mem_singleton.mp ha
        subst a
        have hxx : x = v := by simpa using hx
        have hyy : y = v := by simpa using hy
        subst x
        subst y
        exact (freshChild n freshIdentity v).pool.invariant.closed.refl v |>.trans
          (r.invariant.closed.refl v).symm

/-- Totality of the public order, restricted to actual members. -/
def TotalOnMembers (p : Pool n) : Prop :=
  ∀ x ∈ p.members, ∀ y ∈ p.members,
    p.system.edge x y = true ∨ p.system.edge y x = true

theorem Coherent.child_total {identity : ℕ} {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (ho : (Tree.node identity p children).Coherent)
    (ht : TotalOnMembers p) (a : ℕ × Tree n) (ha : a ∈ children) :
    TotalOnMembers a.2.pool := by
  intro x hx y hy
  rw [ho.restriction a ha x hx y hy, ho.restriction a ha y hy x hx]
  exact ht x ((h.members a ha x).mp hx).1 y ((h.members a ha y).mp hy).1

end SortingAdversary.Optimal.PoolTree.Tree
