import SortingAdversary.Optimal.PoolTreeTraversal
import SortingAdversary.Optimal.TreePromotion

/-!
# Palette caps preserved by actual admissions and promotions

The stronger local invariant counts the labels ever admitted and the labels
already fixed at that node. A new admission increases the former by one;
a promotion increases the latter by one. Each implemented operation inserts
at most one palette position, so the invariant gives the required
`palette size ≤ 2*members + 2` without a supplied asymptotic estimate.
-/

namespace SortingAdversary.Optimal.PoolPalette

open PoolState PoolTree PoolTree.Tree PoolTreeAccounting PoolTreeTraversal

variable {n : ℕ}

def Bounded (p : Pool n) : Prop := p.palette + 1 ≤ p.members.card + p.fixed.card + 2

theorem Bounded.twice {p : Pool n} (h : Bounded p) : p.palette + 1 ≤ 2 * p.members.card + 2 := by
  have hfixed : p.fixed.card ≤ p.members.card := Finset.card_le_card (Finset.filter_subset _ _)
  unfold Bounded at h
  omega

theorem empty_bounded (n : ℕ) : Bounded (emptyPool n) := by
  simp [Bounded, emptyPool, Pool.fixed]

theorem root_bounded (N : ℕ) : Bounded (initialRoot N) := by
  simp [Bounded, initialRoot, Pool.fixed]

theorem admission_fixed_card (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (a : p.Admission v) : a.next.fixed.card = p.fixed.card := by
  have hvfree : v ∉ p.free := fun h => hv (Finset.mem_filter.mp h).1
  have hmem : a.next.members.card = p.members.card + 1 := by
    rw [a.members_eq, Finset.card_insert_of_notMem hv]
  have hfree : a.next.free.card = p.free.card + 1 := by
    rw [Pool.Admission.free_eq p v a, Finset.card_insert_of_notMem hvfree]
  have hp := free_add_fixed p
  have ha := free_add_fixed a.next
  omega

theorem admission_bounded (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (a : p.Admission v) (h : Bounded p) : Bounded a.next := by
  have hmem : a.next.members.card = p.members.card + 1 := by
    rw [a.members_eq, Finset.card_insert_of_notMem hv]
  have hfixed := admission_fixed_card p v hv a
  have hpalette := a.palette_bounds.2
  unfold Bounded at h ⊢
  omega

theorem promotion_fixed_card (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    (p.installPromotion v hv c r).fixed.card = p.fixed.card + 1 := by
  have hfree := p.installPromotion_free_card v hv c r
  have hp := free_add_fixed p
  have hn := free_add_fixed (p.installPromotion v hv c r)
  change (p.installPromotion v hv c r).free.card +
    (p.installPromotion v hv c r).fixed.card = p.members.card at hn
  omega

theorem promotion_bounded (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (h : Bounded p) : Bounded (p.installPromotion v hv c r) := by
  have hfixed := promotion_fixed_card p v hv c r
  have hpalette := r.palette_bounds.2
  unfold Bounded at h ⊢
  change r.palette + 1 ≤ p.members.card + (p.installPromotion v hv c r).fixed.card + 2
  omega

def TreeBounded (t : Tree n) : Prop := ∀ a ∈ storedPools t, Bounded a.2

theorem treeBounded_node_iff (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n)) :
    TreeBounded (.node identity p children) ↔
      Bounded p ∧ ∀ a ∈ children, TreeBounded a.2 := by
  constructor
  · intro h
    constructor
    · exact h _ (by rw [storedPools]; exact List.mem_cons_self)
    · intro child hchild a ha
      apply h a
      rw [storedPools]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, hchild, ha⟩)
  · rintro ⟨hp, hchildren⟩ a ha
    rw [storedPools] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hp
    · obtain ⟨child, hchild, ha⟩ := List.mem_flatMap.mp ha
      exact hchildren child hchild a ha

theorem initial_bounded (N : ℕ) : TreeBounded (initial N) := by
  rw [initial, treeBounded_node_iff]
  exact ⟨root_bounded N, by simp⟩

theorem empty_tree_bounded (n identity : ℕ) : TreeBounded (empty n identity) := by
  rw [empty, treeBounded_node_iff]
  exact ⟨empty_bounded n, by simp⟩

theorem admitRoot_bounded (t : Tree n) (v : Fin n) (hv : v ∉ t.pool.members)
    (h : TreeBounded t) : TreeBounded (t.admitRoot v hv) := by
  cases t with
  | node identity p children =>
    obtain ⟨hp, hchildren⟩ := (treeBounded_node_iff identity p children).mp h
    let a := p.admission v hv
    change TreeBounded (.node identity a.next (mapKeys a.embed children))
    apply (treeBounded_node_iff _ _ _).mpr
    refine ⟨admission_bounded p v hv a hp, ?_⟩
    intro child hchild
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hchild
    exact hchildren old hold

theorem freshChild_bounded (n identity : ℕ) (v : Fin n) :
    TreeBounded (freshChild n identity v) :=
  admitRoot_bounded _ v _ (empty_tree_bounded n identity)

theorem promotedChild_bounded {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × Tree n) (ha : a ∈ children) (hbound : TreeBounded a.2) :
    TreeBounded (promotedChild h v hv c r a ha) := by
  unfold promotedChild
  split
  · exact admitRoot_bounded a.2 v _ hbound
  · exact hbound

/-- The complete implemented parent/child promotion preserves every local
palette cap, including creation and first admission of a fresh child. -/
theorem promotedNode_bounded (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) (hbound : TreeBounded (.node identity p children)) :
    TreeBounded (promotedNode identity p children h v hv c r freshIdentity) := by
  obtain ⟨hp, hchildren⟩ := (treeBounded_node_iff identity p children).mp hbound
  have hnext := promotion_bounded p v hv c r hp
  have hpromoted : ∀ a ∈ promotedChildren h v hv c r, TreeBounded a.2 := by
    intro a ha
    obtain ⟨⟨old, hold⟩, _, rfl⟩ := List.mem_map.mp ha
    exact promotedChild_bounded h v hv c r old hold (hchildren old hold)
  unfold promotedNode
  split
  · exact (treeBounded_node_iff _ _ _).mpr ⟨hnext, hpromoted⟩
  · apply (treeBounded_node_iff _ _ _).mpr
    refine ⟨hnext, ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpromoted a ha
    · have heq := List.mem_singleton.mp ha
      subst a
      exact freshChild_bounded n freshIdentity v

theorem actual_palette_cap {t : Tree n} (h : TreeBounded t) :
    ∀ a ∈ storedPools t, a.2.palette + 1 ≤ 2 * a.2.members.card + 2 :=
  fun a ha => (h a ha).twice

end SortingAdversary.Optimal.PoolPalette
