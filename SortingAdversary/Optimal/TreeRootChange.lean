import SortingAdversary.Optimal.StoppingComparison
import SortingAdversary.Optimal.TreeChronology

/-!
# Root-only artificial-wall changes

A strict cut changes the parent numerical law while preserving membership,
physical pins, palette positions, and every public relation. The existing
children therefore remain exactly the correct children with the same orders.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState PoolPalette TreeChronology
variable {n : ℕ}

theorem pinIndex_none_iff (p : Pool n) (x : Fin n) : pinIndex p x = none ↔ p.pins x = none := by
  simp [pinIndex]

theorem fixed_eq_of_indices (p q : Pool n) (hm : q.members = p.members)
    (hp : ∀ x, pinIndex q x = pinIndex p x) : q.fixed = p.fixed := by
  ext x
  simp only [Pool.fixed, Finset.mem_filter, hm]
  have hn : q.pins x = none ↔ p.pins x = none := by
    rw [← pinIndex_none_iff q x, hp x, pinIndex_none_iff p x]
  exact and_congr Iff.rfl (not_congr hn)

theorem parts_change_root {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (q : Pool n) (hm : q.members = p.members)
    (hk : q.palette = p.palette) (hp : ∀ x, pinIndex q x = pinIndex p x)
    (hs : SeparatedPins.Separated q) : Parts q children := by
  refine ⟨h.keys, ?_, h.occupied, hs, h.children_ok, ?_, ?_⟩
  · intro a ha
    rw [hk]
    exact h.bounds a ha
  · intro a ha x
    rw [hm, hp]
    exact h.members a ha x
  · intro x hx c hc
    rw [hm] at hx
    rw [hp] at hc
    exact h.covered x hx c hc

theorem coherent_change_root (identity : ℕ) (p q : Pool n) (children : List (ℕ × Tree n))
    (ho : (Tree.node identity p children).Coherent) (he : q.system.edge = p.system.edge) :
    (Tree.node identity q children).Coherent := by
  refine .node _ _ _ ho.children ?_
  intro a ha x hx y hy
  rw [he]
  exact ho.restriction a ha x hx y hy

theorem bounded_change_root (identity : ℕ) (p q : Pool n) (children : List (ℕ × Tree n))
    (hb : TreeBounded (Tree.node identity p children)) (hm : q.members = p.members)
    (hk : q.palette = p.palette) (hp : ∀ x, pinIndex q x = pinIndex p x) :
    TreeBounded (Tree.node identity q children) := by
  obtain ⟨hroot, hchildren⟩ := (treeBounded_node_iff _ _ _).mp hb
  apply (treeBounded_node_iff _ _ _).mpr
  refine ⟨?_, hchildren⟩
  unfold Bounded
  rw [hm, hk, fixed_eq_of_indices p q hm hp]
  exact hroot

theorem root_change_retention (identity : ℕ) (p q : Pool n) (children : List (ℕ × Tree n))
    (charge : ℚ) (hr : (p.system.count : ℚ) ≤ charge * q.system.count) :
    ((Tree.node identity p children).count : ℚ) ≤
      charge * (Tree.node identity q children).count := by
  rw [count, count, Nat.cast_mul, Nat.cast_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hr
    (Nat.cast_nonneg (children.map (fun a => a.2.count)).prod : (0 : ℚ) ≤ _)

theorem root_change_identities (identity : ℕ) (p q : Pool n) (children : List (ℕ × Tree n)) :
    identities (Tree.node identity q children) = identities (Tree.node identity p children) := by
  rw [identities_node, identities_node]

theorem root_change_allocated (identity : ℕ) (p q : Pool n) (children : List (ℕ × Tree n))
    (next : ℕ) (ha : Allocated (Tree.node identity p children) next) :
    Allocated (Tree.node identity q children) next := by
  constructor
  · simpa only [root_change_identities identity p q children] using ha.unique
  · simpa only [root_change_identities identity p q children] using ha.below

end SortingAdversary.Optimal.PoolTree.Tree
