import SortingAdversary.Optimal.PoolTreeTraversal
import SortingAdversary.Optimal.PoolPalette
import SortingAdversary.Optimal.TreeOrder
import SortingAdversary.Optimal.CompletedOrder
import SortingAdversary.Optimal.AsymptoticRates

/-!
# Terminal stars-and-bars bound for the coherent stored tree

Totality at the root is inherited by every real child through the checked
public-order restriction. Each node's free labels are sorted by a ranking
extension of that node's actual order; every coordinate outside its free set
is proved fixed by its physical pin. The final result concerns the actual
recursive product count and the actual original-label population.
-/

namespace SortingAdversary.Optimal.TreeTerminal

open scoped BigOperators
open PoolState PoolTree PoolTree.Tree PoolTreeAccounting PoolTreeTraversal
open WeakMaps WeakMaps.WeakSystem

variable {n : ℕ}

theorem poolOrder (p : Pool n) : PublicOrder.IsOrder p.system.edge :=
  ⟨p.invariant.closed.refl, p.invariant.closed.trans, p.invariant.antisymm⟩

noncomputable def poolRanking (p : Pool n) : Ranking n := PublicOrder.rankingExtension p.system.edge

theorem relation_of_rank_le (p : Pool n) (ht : TotalOnMembers p)
    (x : Fin n) (hx : x ∈ p.members) (y : Fin n) (hy : y ∈ p.members)
    (hxy : poolRanking p x ≤ poolRanking p y) : p.system.edge x y = true := by
  have hr := PublicOrder.rankingExtension_respects (poolOrder p)
  rcases ht x hx y hy with hforward | hreverse
  · exact hforward
  · have heq : x = y := (poolRanking p).injective (le_antisymm hxy (hr y x hreverse))
    subst y
    exact p.invariant.closed.refl x

noncomputable def enumerateFree (p : Pool n) : Fin p.free.card → Fin n :=
  CompletedOrder.freeEnumeration (poolRanking p) p.free

theorem enumerateFree_ordered (p : Pool n) (ht : TotalOnMembers p)
    (f : ColorMap (Fin n) (p.palette + 1)) (hf : p.system.Valid f) :
    Monotone (fun i => f (enumerateFree p i)) := by
  intro i j hij
  have hi := CompletedOrder.freeEnumeration_mem (poolRanking p) p.free i
  have hj := CompletedOrder.freeEnumeration_mem (poolRanking p) p.free j
  exact hf.2 _ _ (relation_of_rank_le p ht _ (Finset.mem_filter.mp hi).1 _
    (Finset.mem_filter.mp hj).1
    (CompletedOrder.freeEnumeration_ordered (poolRanking p) p.free hij))

theorem outside_free_fixed (p : Pool n)
    (f : ColorMap (Fin n) (p.palette + 1)) (hf : p.system.Valid f)
    (x : Fin n) (hx : x ∉ p.free) : f x = p.system.lower x := by
  cases hp : p.pins x with
  | none => exact False.elim (hx ((p.free_iff x).mpr hp))
  | some c =>
    exact (p.invariant.pins_valid f hf x c hp).trans (p.pin_bounds x c hp).1.symm

theorem outside_enumeration_fixed (p : Pool n)
    (f : ColorMap (Fin n) (p.palette + 1)) (hf : p.system.Valid f)
    (x : Fin n) (hx : x ∉ Set.range (enumerateFree p)) : f x = p.system.lower x := by
  apply outside_free_fixed p f hf x
  simpa only [enumerateFree, CompletedOrder.range_freeEnumeration, Finset.mem_coe] using hx

/-- Stars and bars applies to this pool's actual represented weak maps. -/
theorem pool_count_le_choose (p : Pool n) (ht : TotalOnMembers p) :
    p.system.count ≤ (p.palette + 1 + p.free.card - 1).choose p.free.card := by
  exact Terminal.card_le_choose_of_fixed_pins p.system.maps (enumerateFree p) p.system.lower
    (fun f hf => enumerateFree_ordered p ht f ((mem_maps p.system f).mp hf))
    (fun f hf => outside_enumeration_fixed p f ((mem_maps p.system f).mp hf))

theorem pool_log_count_le (p : Pool n) (ht : TotalOnMembers p) :
    Real.log (p.system.count : ℝ) ≤
      (p.free.card : ℝ) * (1 + Real.log (1 + ((p.palette + 1 : ℕ) : ℝ) / p.free.card)) :=
  Endpoints.terminal_log_count p.system (enumerateFree p) p.system.lower (by omega) p.count_pos
    (enumerateFree_ordered p ht) (outside_enumeration_fixed p)

/-- Actual public-order coherence transports root totality to every stored
pool, rather than requiring a separate terminal-order premise at each node.
-/
theorem storedPools_total {t : Tree n} (h : t.WellFormed) (hc : t.Coherent)
    (ht : TotalOnMembers t.pool) (a : ℕ × Pool n) (ha : a ∈ storedPools t) :
    TotalOnMembers a.2 := by
  induction h with
  | node identity p children hk hb ho hs hchild hm hcover ih =>
    have hnode := WellFormed.node identity p children hk hb ho hs hchild hm hcover
    rw [storedPools] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ht
    · obtain ⟨child, hchildmem, ha⟩ := List.mem_flatMap.mp ha
      exact ih child hchildmem (hc.children child hchildmem)
        (Coherent.child_total (parts hnode) hc ht child hchildmem) ha

/-- The entire represented tree count is bounded using exactly its original
number of stopping labels and the sum of its actual palette sizes. -/
theorem tree_log_count_le {t : Tree n} (h : t.WellFormed) (hc : t.Coherent)
    (ht : TotalOnMembers t.pool) :
    Real.log (t.count : ℝ) ≤ (t.pool.members.card : ℝ) *
      (1 + Real.log (1 +
        (∑ i : Fin (storedPools t).length, (((poolAt t i).palette + 1 : ℕ) : ℝ)) /
          t.pool.members.card)) := by
  have htotal (i : Fin (storedPools t).length) : TotalOnMembers (poolAt t i) :=
    storedPools_total h hc ht _ (List.get_mem _ _)
  have hterm := Endpoints.terminal_product_log_count
    (fun _ : Fin (storedPools t).length => Fin n)
    (fun i => (poolAt t i).palette + 1) (fun i => (poolAt t i).free.card)
    (fun i => (poolAt t i).system) (fun i => enumerateFree (poolAt t i))
    (fun i => (poolAt t i).system.lower)
    (fun _ => by omega) (fun i => (poolAt t i).count_pos)
    (fun i => enumerateFree_ordered (poolAt t i) (htotal i))
    (fun i => outside_enumeration_fixed (poolAt t i))
  have hprod : (∏ i, ((poolAt t i).system.count : ℝ)) = (t.count : ℝ) := by
    exact_mod_cast prod_poolAt_count h
  have hsum : (∑ i, ((poolAt t i).free.card : ℝ)) = (t.pool.members.card : ℝ) := by
    exact_mod_cast sum_poolAt_free h
  simpa only [hprod, hsum] using hterm

/-- The elementary per-node palette cap gives the actual finite-tree
terminal remainder `s * (1 + log (1 + 4*(s+P)/s))`. -/
theorem tree_log_count_le_population {t : Tree n} (h : t.WellFormed) (hc : t.Coherent)
    (ht : TotalOnMembers t.pool) (hnonempty : t.pool.members.Nonempty)
    (hpalette : ∀ a ∈ storedPools t, a.2.palette + 1 ≤ 2 * a.2.members.card + 2) :
    Real.log (t.count : ℝ) ≤ (t.pool.members.card : ℝ) *
      (1 + Real.log (1 + 4 * ((t.pool.members.card : ℝ) + promotions t) / t.pool.members.card)) := by
  have hterm := tree_log_count_le h hc ht
  have hpal : (∑ i, (((poolAt t i).palette + 1 : ℕ) : ℝ)) ≤ 4 * (t.population : ℝ) := by
    exact_mod_cast sum_palette_le_four_population h hnonempty hpalette
  have hroot : (0 : ℝ) < t.pool.members.card := by exact_mod_cast Finset.card_pos.mpr hnonempty
  have hpalnonneg : 0 ≤ ∑ i, (((poolAt t i).palette + 1 : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have harg : 0 < 1 + (∑ i, (((poolAt t i).palette + 1 : ℕ) : ℝ)) / t.pool.members.card := by
    positivity
  have hlog := Real.log_le_log harg
    (add_le_add le_rfl (div_le_div_of_nonneg_right hpal hroot.le))
  have hbound := hterm.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) hroot.le)
  simpa only [population_eq_members_add_promotions h, Nat.cast_add] using hbound

/-- A correct completed sorter supplies root totality through the actual
transcript. The hypothesis identifies the stored root order with that public
history on its real members; no terminal-chain assumption is needed. -/
theorem root_total_of_correct_run (sorter : DecisionTree n) (hsorter : sorter.Correct)
    (strategy : Strategy n) (past : History n) (π : Ranking n)
    (hπ : Compatible π (sorter.run strategy past).observations) (p : Pool n)
    (hroot : ∀ x ∈ p.members, ∀ y ∈ p.members,
      p.system.edge x y = PublicLegality.publicRows (sorter.run strategy past).observations x y) :
    TotalOnMembers p := by
  intro x hx y hy
  rw [hroot x hx y hy, hroot y hy x hx]
  rcases le_total (π x) (π y) with hxy | hyx
  · exact Or.inl ((CompletedOrder.completed_relation_iff sorter hsorter strategy past π hπ x y).mpr hxy)
  · exact Or.inr ((CompletedOrder.completed_relation_iff sorter hsorter strategy past π hπ y x).mpr hyx)

theorem terminal_count_of_correct_run (sorter : DecisionTree n) (hsorter : sorter.Correct)
    (strategy : Strategy n) (past : History n) (π : Ranking n)
    (hπ : Compatible π (sorter.run strategy past).observations)
    (t : Tree n) (h : t.WellFormed) (hc : t.Coherent) (hnonempty : t.pool.members.Nonempty)
    (hroot : ∀ x ∈ t.pool.members, ∀ y ∈ t.pool.members,
      t.pool.system.edge x y = PublicLegality.publicRows (sorter.run strategy past).observations x y)
    (hpalette : ∀ a ∈ storedPools t, a.2.palette + 1 ≤ 2 * a.2.members.card + 2) :
    Real.log (t.count : ℝ) ≤ (t.pool.members.card : ℝ) *
      (1 + Real.log (1 + 4 * ((t.pool.members.card : ℝ) + promotions t) / t.pool.members.card)) :=
  tree_log_count_le_population h hc
    (root_total_of_correct_run sorter hsorter strategy past π hπ t.pool hroot) hnonempty hpalette

/-- The concrete terminal tree estimate fits the explicit vanishing
`terminalFraction`, after the proved incidence and clock budgets give
`P ≤ 8*s*log s`. -/
theorem normalized_terminal_le {t : Tree n} (h : t.WellFormed) (hc : t.Coherent)
    (ht : TotalOnMembers t.pool) (hsize : 2 ≤ t.pool.members.card)
    (hpalette : ∀ a ∈ storedPools t, a.2.palette + 1 ≤ 2 * a.2.members.card + 2)
    (hpromotions : (promotions t : ℝ) ≤ 8 * t.pool.members.card * Real.log (t.pool.members.card : ℝ)) :
    Real.log (t.count : ℝ) /
        ((t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ)) ≤
      AsymptoticRates.terminalFraction t.pool.members.card := by
  have hn : t.pool.members.Nonempty := Finset.card_pos.mp (by omega)
  have hs : (0 : ℝ) < t.pool.members.card := by exact_mod_cast Finset.card_pos.mpr hn
  have hsone : (1 : ℝ) < t.pool.members.card := by exact_mod_cast (show 1 < t.pool.members.card by omega)
  have hlogpos := Real.log_pos hsone
  have hlogsucc : Real.log (t.pool.members.card : ℝ) ≤ Real.log ((t.pool.members.card : ℝ) + 1) :=
    Real.log_le_log hs (by linarith)
  have hratio : 4 * ((t.pool.members.card : ℝ) + promotions t) / t.pool.members.card ≤
      4 + 32 * Real.log (t.pool.members.card : ℝ) := by
    apply (div_le_iff₀ hs).mpr
    nlinarith
  have harg : 1 + 4 * ((t.pool.members.card : ℝ) + promotions t) / t.pool.members.card ≤
      9 + 64 * Real.log ((t.pool.members.card : ℝ) + 1) := by
    nlinarith
  have hargpos : 0 < 1 + 4 * ((t.pool.members.card : ℝ) + promotions t) / t.pool.members.card := by
    positivity
  have hupper := (tree_log_count_le_population h hc ht hn hpalette).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.log_le_log hargpos harg)) hs.le)
  calc
    _ ≤ ((t.pool.members.card : ℝ) *
        (1 + Real.log (9 + 64 * Real.log ((t.pool.members.card : ℝ) + 1)))) /
        ((t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ)) :=
      div_le_div_of_nonneg_right hupper (mul_pos hs hlogpos).le
    _ = _ := by
      unfold AsymptoticRates.terminalFraction
      field_simp

/-- The palette premise is supplied by the invariant preserved by every
implemented birth and promotion, rather than a separate numerical cap. -/
theorem normalized_terminal_of_bounded {t : Tree n} (h : t.WellFormed) (hc : t.Coherent)
    (ht : TotalOnMembers t.pool) (hsize : 2 ≤ t.pool.members.card)
    (hbound : PoolPalette.TreeBounded t)
    (hpromotions : (promotions t : ℝ) ≤ 8 * t.pool.members.card * Real.log (t.pool.members.card : ℝ)) :
    Real.log (t.count : ℝ) /
        ((t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ)) ≤
      AsymptoticRates.terminalFraction t.pool.members.card :=
  normalized_terminal_le h hc ht hsize (PoolPalette.actual_palette_cap hbound) hpromotions

end SortingAdversary.Optimal.TreeTerminal
