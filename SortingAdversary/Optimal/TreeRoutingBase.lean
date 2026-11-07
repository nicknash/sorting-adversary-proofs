import SortingAdversary.Optimal.TreeOrder
import SortingAdversary.Optimal.TreePromotionCount

/-!
# Public comparison updates at stopping and delegating pools

A stopping answer preserves every old child order by its checked no-inner
condition. An ancestor delegation retains every parent map; only the actual
shared child acquires a new internal relation.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState WeakMaps WeakMaps.WeakSystem ControllerRouting Safety

variable {n : ℕ}

theorem retaining_invariant (p : Pool n) (a b : Fin n)
    (hba : p.system.edge b a ≠ true) (hr : RetainsAll p.system a b) :
    Invariant (closedAdd p.system a b) p.pins := by
  refine ⟨closedAdd_closed p.system p.invariant.closed a b, ?_,
    retaining_feasible p.invariant hr, ?_, ?_⟩
  · intro x y hxy hyx
    exact Routing.adjoin_antisymmetric
      (fun {u v w} huv hvw => p.invariant.closed.trans u v w huv hvw)
      p.invariant.antisymm hba x y
      ((closedAdd_edge _ _ _ _ _).mp hxy) ((closedAdd_edge _ _ _ _ _).mp hyx)
  · intro f hf
    exact p.invariant.pins_valid f ((closedAdd_valid _ p.invariant.closed a b f).mp hf).1
  · intro v hv
    obtain ⟨hl, hu⟩ := retained_windows p.system p.invariant.closed p.invariant.feasible hr v
    rw [hl, hu]
    exact p.invariant.free_window v hv

theorem retaining_count (p : Pool n) (a b : Fin n) (hr : RetainsAll p.system a b) :
    (closedAdd p.system a b).count = p.system.count := by
  apply congrArg Finset.card
  ext f
  simp only [mem_maps, closedAdd_valid _ p.invariant.closed]
  exact ⟨And.left, fun hf => ⟨hf, hr f hf⟩⟩

/-- Store the new closed public row without changing primitive lists or pins. -/
def addComparison (p : Pool n) (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins) : Pool n where
  palette := p.palette
  positive := p.positive
  members := p.members
  system := closedAdd p.system a b
  pins := p.pins
  invariant := hi
  pin_bounds := p.pin_bounds
  capacity := p.capacity
  outside := by
    intro x hx
    obtain ⟨hp, hu⟩ := p.outside x hx
    refine ⟨hp, hu.lower, hu.upper, ?_, ?_⟩
    · intro y hxy
      rcases (closedAdd_edge _ _ _ _ _).mp hxy with hold | ⟨hxa, _⟩
      · exact hu.outgoing y hold
      · exact False.elim (hx ((hu.outgoing a hxa) ▸ ha))
    · intro y hyx
      rcases (closedAdd_edge _ _ _ _ _).mp hyx with hold | ⟨_, hbx⟩
      · exact hu.incoming y hold
      · exact False.elim (hx ((hu.incoming b hbx) ▸ hb))

theorem addComparison_separated (p : Pool n) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins) (hs : SeparatedPins.Separated p) :
    SeparatedPins.Separated (addComparison p a b ha hb hi) := by
  intro x hx c hp
  obtain ⟨y, hy, hcomp, hpin⟩ := hs x hx c hp
  refine ⟨y, hy, ?_, hpin⟩
  exact hcomp.elim (fun h => Or.inl ((closedAdd_edge _ _ _ _ _).mpr (Or.inl h)))
    (fun h => Or.inr ((closedAdd_edge _ _ _ _ _).mpr (Or.inl h)))

theorem same_child_retains {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (child : ℕ × Tree n) (hchild : child ∈ children)
    (a b : Fin n) (ha : a ∈ child.2.pool.members) (hb : b ∈ child.2.pool.members) :
    RetainsAll p.system a b := by
  obtain ⟨c, hca, hc⟩ := h.pin_witness child hchild a ha
  obtain ⟨d, hdb, hd⟩ := h.pin_witness child hchild b hb
  have hcd : c = d := Fin.ext (hc.trans hd.symm)
  intro f hf
  rw [p.invariant.pins_valid f hf a c hca, p.invariant.pins_valid f hf b d hdb, hcd]

theorem safe_child_unchanged {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (a b : Fin n) (hs : ¬ Inner p.system p.pins a b)
    (child : ℕ × Tree n) (hchild : child ∈ children)
    (x : Fin n) (hx : x ∈ child.2.pool.members)
    (y : Fin n) (hy : y ∈ child.2.pool.members) :
    (closedAdd p.system a b).edge x y = p.system.edge x y := by
  apply Bool.eq_iff_iff.mpr
  rw [closedAdd_edge]
  constructor
  · rintro (hold | ⟨hxa, hby⟩)
    · exact hold
    · by_contra hxy
      obtain ⟨c, hcx, hc⟩ := h.pin_witness child hchild x hx
      obtain ⟨d, hdy, hd⟩ := h.pin_witness child hchild y hy
      have hcd : c = d := Fin.ext (hc.trans hd.symm)
      apply hs
      exact ⟨x, y, c, hcx, hcd.symm ▸ hdy, hxa, hby, hxy⟩
  · exact Or.inl

theorem other_child_unchanged {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (target : ℕ × Tree n) (htarget : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (child : ℕ × Tree n) (hchild : child ∈ children) (hne : child.1 ≠ target.1)
    (x : Fin n) (hx : x ∈ child.2.pool.members)
    (y : Fin n) (hy : y ∈ child.2.pool.members) :
    (closedAdd p.system a b).edge x y = p.system.edge x y := by
  apply Bool.eq_iff_iff.mpr
  rw [closedAdd_edge]
  constructor
  · rintro (hold | ⟨hxa, hby⟩)
    · exact hold
    · obtain ⟨c, hca, hc⟩ := h.pin_witness target htarget a ha
      obtain ⟨d, hdb, hd⟩ := h.pin_witness target htarget b hb
      obtain ⟨e, hex, he⟩ := h.pin_witness child hchild x hx
      obtain ⟨f, hfy, hf⟩ := h.pin_witness child hchild y hy
      have hcd : c = d := Fin.ext (hc.trans hd.symm)
      have hef : e = f := Fin.ext (he.trans hf.symm)
      obtain ⟨g, hg⟩ := p.invariant.feasible
      have h1 := hg.2 x a hxa
      have h2 := hg.2 b y hby
      rw [p.invariant.pins_valid g hg x e hex, p.invariant.pins_valid g hg a c hca] at h1
      rw [p.invariant.pins_valid g hg b d hdb, p.invariant.pins_valid g hg y f hfy,
        ← hcd, ← hef] at h2
      have hec := le_antisymm h1 h2
      exact False.elim (hne (he.symm.trans ((congrArg Fin.val hec).trans hc)))
  · exact Or.inl

theorem same_child_closedAdd {identity : ℕ} {p : Pool n}
    {children : List (ℕ × Tree n)} (ho : (Tree.node identity p children).Coherent)
    (child : ℕ × Tree n) (hchild : child ∈ children)
    (a b : Fin n) (ha : a ∈ child.2.pool.members) (hb : b ∈ child.2.pool.members)
    (x : Fin n) (hx : x ∈ child.2.pool.members)
    (y : Fin n) (hy : y ∈ child.2.pool.members) :
    (closedAdd child.2.pool.system a b).edge x y = (closedAdd p.system a b).edge x y := by
  simp only [closedAdd, ho.restriction child hchild x hx y hy,
    ho.restriction child hchild x hx a ha, ho.restriction child hchild b hb y hy]

def stopNode (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins) : Tree n :=
  .node identity (addComparison p a b ha hb hi) children

theorem stopNode_wellFormed (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins) :
    (stopNode identity p children a b ha hb hi).WellFormed :=
  .node _ _ _ h.keys h.bounds h.occupied
    (addComparison_separated p a b ha hb hi h.separated) h.children_ok h.members h.covered

theorem stopNode_coherent (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (ho : (Tree.node identity p children).Coherent)
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins) (hs : ¬ Inner p.system p.pins a b) :
    (stopNode identity p children a b ha hb hi).Coherent := by
  refine .node _ _ _ ho.children ?_
  intro child hchild x hx y hy
  exact (ho.restriction child hchild x hx y hy).trans
    (safe_child_unchanged h a b hs child hchild x hx y hy).symm

end SortingAdversary.Optimal.PoolTree.Tree
