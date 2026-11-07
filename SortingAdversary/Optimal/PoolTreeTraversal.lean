import SortingAdversary.Optimal.PoolTreeGroups

/-!
# Exact traversal identities for stored pools

Traversal positions are finite indices used only for summation. Every entry
also retains its immutable natural-number node identity. No uniqueness of
those identities is silently inferred from the current preorder position.
-/

namespace SortingAdversary.Optimal.PoolTreeTraversal

open scoped BigOperators
open PoolState PoolTree PoolTree.Tree PoolTreeAccounting PoolTreeGroups

theorem sum_map_flatMap {α β M : Type*} [AddMonoid M]
    (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).sum = (l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem prod_map_flatMap {α β M : Type*} [Monoid M]
    (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).prod = (l.map (fun a => ((g a).map f).prod)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

theorem prod_map_get {α M : Type*} [CommMonoid M] (l : List α) (f : α → M) :
    (l.map f).prod = ∏ i : Fin l.length, f (l.get i) := by
  simpa only [List.get_eq_getElem, List.ofFn_getElem_eq_map] using
    (List.prod_ofFn (f := fun i : Fin l.length => f (l.get i)))

variable {n : ℕ}

def storedPools : Tree n → List (ℕ × Pool n)
  | .node identity p children => (identity, p) :: children.flatMap (fun a => storedPools a.2)
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

def poolAt (t : Tree n) (i : Fin (storedPools t).length) : Pool n := ((storedPools t).get i).2

def identityAt (t : Tree n) (i : Fin (storedPools t).length) : ℕ := ((storedPools t).get i).1

theorem storedPools_sum_node {M : Type*} [AddMonoid M]
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n)) (f : ℕ × Pool n → M) :
    ((storedPools (.node identity p children)).map f).sum =
      f (identity, p) + (children.map (fun a => ((storedPools a.2).map f).sum)).sum := by
  rw [storedPools]
  simp only [List.map_cons, List.sum_cons, sum_map_flatMap]

theorem storedPools_prod_node {M : Type*} [Monoid M]
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n)) (f : ℕ × Pool n → M) :
    ((storedPools (.node identity p children)).map f).prod =
      f (identity, p) * (children.map (fun a => ((storedPools a.2).map f).prod)).prod := by
  rw [storedPools]
  simp only [List.map_cons, List.prod_cons, prod_map_flatMap]

theorem storedPools_length {t : Tree n} (h : t.WellFormed) : (storedPools t).length = t.nodes := by
  induction h with
  | node _ _ _ _ _ _ _ _ _ _ ih =>
    rw [storedPools, nodes]
    simp only [List.length_cons, List.length_flatMap]
    rw [List.map_congr_left (fun a ha => ih a ha)]
    omega

theorem storedPools_count {t : Tree n} (h : t.WellFormed) :
    ((storedPools t).map (fun a => a.2.system.count)).prod = t.count := by
  induction h with
  | node _ _ _ _ _ _ _ _ _ _ ih =>
    rw [storedPools_prod_node, count, List.map_congr_left (fun a ha => ih a ha)]

theorem storedPools_population {t : Tree n} (h : t.WellFormed) :
    ((storedPools t).map (fun a => a.2.members.card)).sum = t.population := by
  induction h with
  | node _ _ _ _ _ _ _ _ _ _ ih =>
    rw [storedPools_sum_node, population, List.map_congr_left (fun a ha => ih a ha)]

theorem storedPools_stopping {t : Tree n} (h : t.WellFormed) :
    ((storedPools t).map (fun a => a.2.free.card)).sum = t.pool.members.card := by
  have hsum : ((storedPools t).map (fun a => a.2.free.card)).sum = stoppingPopulation t := by
    induction h with
    | node _ _ _ _ _ _ _ _ _ _ ih =>
      rw [storedPools_sum_node, stoppingPopulation, List.map_congr_left (fun a ha => ih a ha)]
  exact hsum.trans (stoppingPopulation_eq_members h)

theorem storedPools_promotions {t : Tree n} (h : t.WellFormed) :
    ((storedPools t).map (fun a => a.2.fixed.card)).sum = promotions t := by
  induction h with
  | node _ _ _ _ _ _ _ _ _ _ ih =>
    rw [storedPools_sum_node, promotions, List.map_congr_left (fun a ha => ih a ha)]

/-- Reservation destination entropy summed over the actual stored pools is
exactly the entropy proved to be at most `s log s`. -/
theorem storedPools_entropy {t : Tree n} (h : t.WellFormed) :
    ((storedPools t).map (fun a => localEntropy a.2)).sum = PoolTreeAccounting.entropy t := by
  induction h with
  | node identity p children hk hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hk hb ho hs hchild hm hc
    rw [storedPools_sum_node, entropy_eq_local_add_children hnode,
      List.map_congr_left (fun a ha => ih a ha)]

theorem storedPools_nonempty {t : Tree n} (h : t.WellFormed) (hnonempty : t.pool.members.Nonempty)
    (a : ℕ × Pool n) (ha : a ∈ storedPools t) : a.2.members.Nonempty := by
  induction h with
  | node _ _ children _ _ ho _ _ _ _ ih =>
    rw [storedPools] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hnonempty
    · obtain ⟨child, hchild, ha⟩ := List.mem_flatMap.mp ha
      exact ih child hchild (ho child hchild) ha

theorem sum_poolAt_members {t : Tree n} (h : t.WellFormed) :
    (∑ i, (poolAt t i).members.card) = t.population := by
  simpa only [sum_map_get, poolAt] using storedPools_population h

theorem sum_poolAt_free {t : Tree n} (h : t.WellFormed) :
    (∑ i, (poolAt t i).free.card) = t.pool.members.card := by
  simpa only [sum_map_get, poolAt] using storedPools_stopping h

theorem prod_poolAt_count {t : Tree n} (h : t.WellFormed) :
    (∏ i, (poolAt t i).system.count) = t.count := by
  simpa only [prod_map_get, poolAt] using storedPools_count h

theorem sum_poolAt_entropy {t : Tree n} (h : t.WellFormed) :
    (∑ i, localEntropy (poolAt t i)) = PoolTreeAccounting.entropy t := by
  simpa only [sum_map_get, poolAt] using storedPools_entropy h

theorem sum_palette_le_four_population {t : Tree n} (h : t.WellFormed)
    (hnonempty : t.pool.members.Nonempty)
    (hpalette : ∀ a ∈ storedPools t, a.2.palette + 1 ≤ 2 * a.2.members.card + 2) :
    (∑ i, ((poolAt t i).palette + 1)) ≤ 4 * t.population := by
  have hlocal (i : Fin (storedPools t).length) :
      (poolAt t i).palette + 1 ≤ 4 * (poolAt t i).members.card := by
    have hc := hpalette ((storedPools t).get i) (List.get_mem _ _)
    have hp := Finset.card_pos.mpr
      (storedPools_nonempty h hnonempty ((storedPools t).get i) (List.get_mem _ _))
    change (poolAt t i).palette + 1 ≤ 2 * (poolAt t i).members.card + 2 at hc
    change 0 < (poolAt t i).members.card at hp
    omega
  calc
    _ ≤ ∑ i, 4 * (poolAt t i).members.card := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = _ := by rw [← Finset.mul_sum, sum_poolAt_members h]

end SortingAdversary.Optimal.PoolTreeTraversal
