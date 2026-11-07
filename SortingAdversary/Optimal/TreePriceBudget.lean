import SortingAdversary.Optimal.StoredStateIndex
import SortingAdversary.Optimal.TreeFactorialCredit
import SortingAdversary.Optimal.SignedPrice

/-!
# Actual final-tree destinations and dictionary capacity

A destination is a real stored node and an immutable palette identity. Its
population is the physical pin fibre at that node. Empty palette identities
contribute zero. Occupied destinations correspond exactly to actual child
populations, so the global population, factorial, and entropy sums concern
the concrete final tree.
-/

namespace SortingAdversary.Optimal.TreePriceBudget

open scoped BigOperators
open PoolState WidthRepair PoolTree.Tree PoolTreeAccounting PoolTreeTraversal PoolTreeGroups
open StoredStateIndex TreeFactorialCredit

variable {n : ℕ}

abbrev Slot (t : StoredTree n) := Σ i : StateIndex t, Fin ((stateAt t i).pool.palette + 1)

def population (t : StoredTree n) (c : Slot t) : ℕ :=
  (pinFiber (stateAt t c.1).pool ((stateAt t c.1).order c.2)).card

def destinations (t : StoredTree n) : Finset (Slot t) :=
  Finset.univ.filter (fun c => 0 < population t c)

def exponent (t : StoredTree n) (i : StateIndex t) : ℕ :=
  Nat.clog 2 ((stateAt t i).pool.palette + 1)

theorem exponent_covers (t : StoredTree n) (i : StateIndex t) :
    (stateAt t i).pool.palette + 1 ≤ 2 ^ exponent t i := Nat.le_pow_clog (by decide) _

theorem pow_clog_le_twice {k : ℕ} (hk : 0 < k) : 2 ^ Nat.clog 2 k ≤ 2 * k := by
  by_cases h : k = 1
  · simp [h]
  have hk1 : 1 < k := by omega
  have hc := Nat.clog_pos (by decide : 1 < 2) hk1
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hk1
  rw [← Nat.succ_pred_eq_of_pos hc, pow_succ]
  omega

theorem state_nonempty (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : t.pool.members.Nonempty) (i : StateIndex t) : (stateAt t i).pool.members.Nonempty :=
  storedPools_nonempty hw (by simpa only [StoredTree.erase_pool] using hn)
    _ (stateAt_pool_mem t i)

theorem capacity_le_eight_members (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : t.pool.members.Nonempty) (bounded : PoolPalette.TreeBounded t.erase) (i : StateIndex t) :
    2 ^ exponent t i ≤ 8 * (stateAt t i).pool.members.card := by
  have hp := (bounded _ (stateAt_pool_mem t i)).twice
  dsimp only at hp
  have hm : 0 < (stateAt t i).pool.members.card := Finset.card_pos.mpr (state_nonempty t hw hn i)
  have hc := pow_clog_le_twice (Nat.succ_pos (stateAt t i).pool.palette)
  simp only [Nat.succ_eq_add_one] at hc
  unfold exponent
  omega

theorem totalCapacity_le (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : t.pool.members.Nonempty) (bounded : PoolPalette.TreeBounded t.erase) :
    DyadicDictionary.totalCapacity (exponent t) ≤
      8 * (t.pool.members.card + promotions t.erase) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (StateIndex t))) =>
    capacity_le_eight_members t hw hn bounded i)
  rw [← Finset.mul_sum, sum_members t hw,
    population_eq_members_add_promotions hw, StoredTree.erase_pool] at h
  exact h

theorem pin_sum_children {M : Type*} [AddCommMonoid M]
    {identity : ℕ} {p : Pool n} {children : List (ℕ × PoolTree.Tree n)}
    (hw : (PoolTree.Tree.node identity p children).WellFormed) (f : ℕ → M) (hzero : f 0 = 0) :
    (∑ c : Fin (p.palette + 1), f (pinFiber p c).card) =
      (children.map (fun a => f a.2.pool.members.card)).sum := by
  rw [sum_map_get]
  apply (Fintype.sum_of_injective (childColor hw) (childColor_injective hw)
    (fun i => f (childMembers children i).card) (fun c => f (pinFiber p c).card) ?_ ?_).symm
  · intro c hc
    simp only [pinFiber_empty_of_unoccupied hw c hc, Finset.card_empty, hzero]
  · intro i
    rw [pinFiber_childColor hw i]

theorem stored_pin_sum {M : Type*} [AddCommMonoid M] (t : PoolTree.Tree n) (hw : t.WellFormed)
    (f : ℕ → M) (hzero : f 0 = 0) :
    ((storedPools t).map (fun a => ∑ c : Fin (a.2.palette + 1), f (pinFiber a.2 c).card)).sum =
      ((storedPools t).tail.map (fun a => f a.2.members.card)).sum := by
  induction hw with
  | node identity p children hk hb ho hs hchild hm hc ih =>
    have hnode := WellFormed.node identity p children hk hb ho hs hchild hm hc
    rw [storedPools_sum_node, pin_sum_children hnode f hzero]
    have hchildsum (a : ℕ × PoolTree.Tree n) (ha : a ∈ children) :
        f a.2.pool.members.card +
          ((storedPools a.2).map (fun b => ∑ c : Fin (b.2.palette + 1), f (pinFiber b.2 c).card)).sum =
        ((storedPools a.2).map (fun b => f b.2.members.card)).sum := by
      rw [ih a ha]
      cases he : a.2 with
      | node _ _ _ => simp only [storedPools, List.tail_cons, List.map_cons, List.sum_cons, PoolTree.Tree.pool]
    rw [← List.sum_map_add]
    rw [List.map_congr_left hchildsum]
    rw [storedPools]
    simp only [List.tail_cons, sum_map_flatMap]

theorem sum_slots {M : Type*} [AddCommMonoid M] (t : StoredTree n) (hw : t.erase.WellFormed)
    (f : ℕ → M) (hzero : f 0 = 0) :
    (∑ c : Slot t, f (population t c)) =
      ((storedPools t.erase).tail.map (fun a => f a.2.members.card)).sum := by
  rw [Fintype.sum_sigma]
  have hlocal (i : StateIndex t) :
      (∑ c : Fin ((stateAt t i).pool.palette + 1), f (population t ⟨i, c⟩)) =
        ∑ c : Fin ((stateAt t i).pool.palette + 1), f (pinFiber (stateAt t i).pool c).card := by
    exact Equiv.sum_comp (stateAt t i).order (fun c => f (pinFiber (stateAt t i).pool c).card)
  simp_rw [hlocal]
  rw [sum_stateAt t (fun p => ∑ c : Fin (p.palette + 1), f (pinFiber p c).card)]
  exact stored_pin_sum t.erase hw f hzero

theorem sum_destinations {M : Type*} [AddCommMonoid M] (t : StoredTree n) (f : ℕ → M)
    (hzero : f 0 = 0) :
    (∑ c ∈ destinations t, f (population t c)) = ∑ c : Slot t, f (population t c) := by
  unfold destinations
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hout
  have hz : population t c = 0 := by
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨hc, Nat.pos_of_ne_zero h⟩)
  simp only [hz, hzero]

theorem total_population (t : StoredTree n) (hw : t.erase.WellFormed) :
    (∑ c : Slot t, population t c) = promotions t.erase := by
  have hs := sum_slots t hw id rfl
  simp only [id_eq] at hs
  rw [hs]
  have hp := storedPools_population hw
  have hparts : ((storedPools t.erase).map (fun a => a.2.members.card)).sum =
      t.erase.pool.members.card + ((storedPools t.erase).tail.map (fun a => a.2.members.card)).sum := by
    cases t.erase
    simp only [storedPools, List.map_cons, List.sum_cons, List.tail_cons, PoolTree.Tree.pool]
  rw [hparts, population_eq_members_add_promotions hw] at hp
  exact Nat.add_left_cancel hp

theorem factorial_sum (t : StoredTree n) (hw : t.erase.WellFormed) :
    (∑ c : Slot t, Real.log ((population t c).factorial : ℝ)) = nonrootFactorial t.erase := by
  exact sum_slots t hw (fun k => Real.log (k.factorial : ℝ)) (by simp)

theorem destination_card (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : t.pool.members.Nonempty) : (destinations t).card + 1 = t.erase.nodes := by
  let indicator : ℕ → ℕ := fun k => if 0 < k then 1 else 0
  have hsum := sum_slots t hw indicator (by simp [indicator])
  have hleft : (∑ c : Slot t, indicator (population t c)) = (destinations t).card := by
    simp [indicator, destinations]
  rw [hleft] at hsum
  have hpositive (a : ℕ × Pool n) (ha : a ∈ (storedPools t.erase).tail) :
      indicator a.2.members.card = 1 := by
    have hmem := storedPools_nonempty hw (by simpa only [StoredTree.erase_pool] using hn)
      a (List.mem_of_mem_tail ha)
    simp [indicator, Finset.card_pos.mpr hmem]
  have hright : ((storedPools t.erase).tail.map (fun a => indicator a.2.members.card)).sum =
      (storedPools t.erase).tail.length := by
    rw [List.map_congr_left hpositive]
    simp
  rw [hright] at hsum
  have hlen := storedPools_length hw
  have hpos := storedStates_nonempty t
  rw [storedStates_length] at hpos
  simp only [List.length_tail] at hsum
  omega

theorem destination_card_le (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : t.pool.members.Nonempty) : (destinations t).card ≤ 2 * t.pool.members.card := by
  have hc := destination_card t hw hn
  have ht := nodes_add_one_le_twice_members hw (by simpa only [StoredTree.erase_pool] using hn)
  rw [StoredTree.erase_pool] at ht
  omega

end SortingAdversary.Optimal.TreePriceBudget
