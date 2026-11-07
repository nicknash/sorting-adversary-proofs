import SortingAdversary.Optimal.RepresentationTreePromotion
import SortingAdversary.Optimal.StoredRepair

/-! # Actual finite shape bounds used by measured tree replay -/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState PoolPalette

variable {n : ℕ}

def treeShapeBound (n : ℕ) : ℕ := 2 * n + 2

theorem bounded_palette_size (p : Pool n) (h : Bounded p) : p.palette + 1 ≤ treeShapeBound n := by
  have hc : p.members.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ p.members
  exact h.twice.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 2)

theorem stored_palette_size (t : StoredTree n) (h : TreeBounded t.erase) :
    t.pool.palette + 1 ≤ treeShapeBound n := by
  cases t with
  | node identity p d children =>
    rw [StoredTree.erase] at h
    change TreeBounded (.node identity p (StoredTree.erasedChildren children)) at h
    exact bounded_palette_size p ((treeBounded_node_iff ..).mp h).1

theorem parts_children_length {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (StoredTree.erasedChildren children)) : children.length ≤ p.palette + 1 := by
  have hk : (children.map Prod.fst).Nodup := by
    simpa only [StoredTree.erasedChildren, List.map_map, Function.comp_def] using h.keys
  have subset : (children.map Prod.fst).toFinset ⊆ Finset.range (p.palette + 1) := by
    intro x hx
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact Finset.mem_range.mpr (h.bounds (entry.1, entry.2.erase)
      (List.mem_map.mpr ⟨entry, he, rfl⟩))
  have hc := Finset.card_le_card subset
  simpa only [List.toFinset_card_of_nodup hk, List.length_map, Finset.card_range] using hc

theorem stored_children_length (t : StoredTree n) (hw : t.erase.WellFormed)
    (hb : TreeBounded t.erase) : rootChildrenLength t ≤ treeShapeBound n := by
  have hp := stored_palette_size t hb
  cases t with
  | node identity p d children =>
    rw [StoredTree.erase] at hw
    change (PoolTree.Tree.node identity p (StoredTree.erasedChildren children)).WellFormed at hw
    exact (parts_children_length (PoolTree.Tree.parts hw)).trans hp

theorem node_child_bounds (identity : ℕ) (s : State n) {children : List (ℕ × StoredTree n)}
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (hb : TreeBounded (StoredRepair.node identity s children).erase) :
    (∀ entry ∈ children, entry.2.pool.palette ≤ treeShapeBound n) ∧
      (∀ entry ∈ children, rootChildrenLength entry.2 ≤ treeShapeBound n) := by
  rw [StoredRepair.erase_node] at hw hb
  have parts := PoolTree.Tree.parts hw
  have childBounds := ((treeBounded_node_iff ..).mp hb).2
  constructor
  · intro entry he
    have hm : (entry.1, entry.2.erase) ∈ StoredTree.erasedChildren children :=
      List.mem_map.mpr ⟨entry, he, rfl⟩
    have hc := stored_palette_size entry.2 (childBounds _ hm)
    omega
  · intro entry he
    have hm : (entry.1, entry.2.erase) ∈ StoredTree.erasedChildren children :=
      List.mem_map.mpr ⟨entry, he, rfl⟩
    exact stored_children_length entry.2 (parts.children_ok _ hm) (childBounds _ hm)

end SortingAdversary.Optimal.RepresentationWork
