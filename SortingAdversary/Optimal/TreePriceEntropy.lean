import SortingAdversary.Optimal.TreePriceBudget

/-!
# Population entropy of actual final destinations

Any selected multiplicity is bounded by its actual physical pin fibre. Its
dictionary entropy is consequently controlled by the real tree separation
entropy, the total child population, and one fixed logarithmic factor per
selected event. The resulting capacity budget is uniform in the stage.
-/

namespace SortingAdversary.Optimal.TreePriceBudget

open scoped BigOperators
open PoolState PoolTreeAccounting PoolTreeTraversal PoolTreeGroups StoredStateIndex

variable {n : ℕ}

theorem population_le_members (t : StoredTree n) (c : Slot t) :
    population t c ≤ (stateAt t c.1).pool.members.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem population_le_capacity (t : StoredTree n) (c : Slot t) :
    population t c ≤ 2 ^ exponent t c.1 :=
  (population_le_members t c).trans ((stateAt t c.1).pool.capacity.trans (exponent_covers t c.1))

theorem population_entropy_nonneg {m s : ℝ} (hm : 0 ≤ m) (hms : m ≤ s) :
    0 ≤ m * Real.log (s / m) := by
  by_cases hz : m = 0
  · simp [hz]
  have hp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
  exact mul_nonneg hm (Real.log_nonneg ((one_le_div hp).mpr hms))

theorem selected_entropy_term {C s m k : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hk : 0 ≤ k) (hkm : k ≤ m) (hms : m ≤ s)
    (hcap : C ≤ 8 * s) :
    k * Real.log (C / k) ≤ m * Real.log (s / m) + m + k * Real.log 8 := by
  by_cases hz : k = 0
  · simp only [hz, zero_mul, add_zero]
    exact add_nonneg (population_entropy_nonneg hm hms) hm
  have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm hz)
  have hmp : 0 < m := hkp.trans_le hkm
  have hsp : 0 < s := hmp.trans_le hms
  have hlogsm : 0 ≤ Real.log (s / m) := Real.log_nonneg ((one_le_div hmp).mpr hms)
  have hsmall := mul_le_mul_of_nonneg_right hkm hlogsm
  have ht := Real.log_le_sub_one_of_pos (div_pos hmp hkp)
  have ht' := mul_le_mul_of_nonneg_left ht hk
  have hcancel : k * (m / k - 1) = m - k := by field_simp
  rw [hcancel] at ht'
  have hlarge := Real.log_le_log (div_pos hC hkp)
    (div_le_div_of_nonneg_right hcap hk)
  have hlarge' := mul_le_mul_of_nonneg_left hlarge hk
  have hsplit : Real.log (8 * s / k) = Real.log 8 + Real.log (s / m) + Real.log (m / k) := by
    rw [Real.log_div (mul_pos (by norm_num) hsp).ne' hkp.ne',
      Real.log_mul (by norm_num) hsp.ne', Real.log_div hsp.ne' hmp.ne',
      Real.log_div hmp.ne' hkp.ne']
    ring
  rw [hsplit] at hlarge'
  nlinarith

theorem slot_entropy (t : StoredTree n) (hw : t.erase.WellFormed) :
    (∑ c : Slot t, (population t c : ℝ) *
      Real.log ((stateAt t c.1).pool.members.card / (population t c : ℝ))) = entropy t.erase := by
  rw [Fintype.sum_sigma]
  have hlocal (i : StateIndex t) :
      (∑ c : Fin ((stateAt t i).pool.palette + 1),
        (population t ⟨i, c⟩ : ℝ) *
          Real.log ((stateAt t i).pool.members.card / (population t ⟨i, c⟩ : ℝ))) =
        localEntropy (stateAt t i).pool := by
    unfold population localEntropy GroupReservations.destinationEntropy
    simp only [fixedDestination_card]
    exact Equiv.sum_comp (stateAt t i).order (fun c =>
      ((pinFiber (stateAt t i).pool c).card : ℝ) *
        Real.log ((stateAt t i).pool.members.card / ((pinFiber (stateAt t i).pool c).card : ℝ)))
  simp_rw [hlocal]
  exact sum_entropy t hw

noncomputable def selectedEntropy (t : StoredTree n) (hubs : Slot t → ℕ) : ℝ :=
  ∑ c : Slot t, (hubs c : ℝ) * Real.log ((2 : ℝ) ^ exponent t c.1 / hubs c)

theorem selectedEntropy_nonneg (t : StoredTree n) (hubs : Slot t → ℕ)
    (bounded : ∀ c, hubs c ≤ population t c) : 0 ≤ selectedEntropy t hubs := by
  apply Finset.sum_nonneg
  intro c _
  apply population_entropy_nonneg (Nat.cast_nonneg _)
  exact_mod_cast (bounded c).trans (population_le_capacity t c)

theorem selectedEntropy_le (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : t.pool.members.Nonempty) (palette : PoolPalette.TreeBounded t.erase)
    (hubs : Slot t → ℕ) (bounded : ∀ c, hubs c ≤ population t c) :
    selectedEntropy t hubs ≤ entropy t.erase + promotions t.erase +
      (∑ c : Slot t, (hubs c : ℝ)) * Real.log 8 := by
  have hterm (c : Slot t) :
      (hubs c : ℝ) * Real.log ((2 : ℝ) ^ exponent t c.1 / hubs c) ≤
        (population t c : ℝ) * Real.log ((stateAt t c.1).pool.members.card / (population t c : ℝ)) +
          population t c + (hubs c : ℝ) * Real.log 8 := by
    apply selected_entropy_term (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact_mod_cast bounded c
    · exact_mod_cast population_le_members t c
    · exact_mod_cast capacity_le_eight_members t hw hn palette c.1
  have hs := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Slot t))) => hterm c)
  have hpop : (∑ c : Slot t, (population t c : ℝ)) = promotions t.erase := by
    exact_mod_cast total_population t hw
  simpa only [selectedEntropy, Finset.sum_add_distrib, ← Finset.sum_mul,
    slot_entropy t hw, hpop] using hs

noncomputable def dictionaryBudget (t : StoredTree n) (hubs : Slot t → ℕ) : ℝ :=
  DyadicDictionary.totalCapacity (exponent t) + selectedEntropy t hubs

theorem dictionaryBudget_nonneg (t : StoredTree n) (hubs : Slot t → ℕ)
    (bounded : ∀ c, hubs c ≤ population t c) : 0 ≤ dictionaryBudget t hubs :=
  add_nonneg (Nat.cast_nonneg _) (selectedEntropy_nonneg t hubs bounded)

theorem dictionaryBudget_le (t : StoredTree n) (hw : t.erase.WellFormed)
    (hn : 2 ≤ t.pool.members.card) (palette : PoolPalette.TreeBounded t.erase)
    (hubs : Slot t → ℕ) (bounded : ∀ c, hubs c ≤ population t c)
    (hprom : (promotions t.erase : ℝ) ≤
      8 * ((t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ)))
    (hmass : (∑ c : Slot t, (hubs c : ℝ)) ≤
      8 * ((t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ))) :
    dictionaryBudget t hubs ≤ 256 * ((t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ)) := by
  have hnonempty : t.pool.members.Nonempty := Finset.card_pos.mp (by omega)
  let T : ℝ := (t.pool.members.card : ℝ) * Real.log (t.pool.members.card : ℝ)
  let X : ℝ := ∑ c : Slot t, (hubs c : ℝ)
  let K : ℝ := DyadicDictionary.totalCapacity (exponent t)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t.pool.members.card by omega)))
  have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hnT : (t.pool.members.card : ℝ) ≤ 2 * T := by
    have hnreal : (2 : ℝ) ≤ t.pool.members.card := by exact_mod_cast hn
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnreal
    have hm := mul_le_mul_of_nonneg_left (AsymptoticRates.half_le_log_two.trans hl)
      (Nat.cast_nonneg t.pool.members.card : (0 : ℝ) ≤ t.pool.members.card)
    dsimp [T]
    nlinarith
  have hK : K ≤ 8 * ((t.pool.members.card : ℝ) + promotions t.erase) := by
    dsimp only [K]
    exact_mod_cast totalCapacity_le t hw hnonempty palette
  have he := selectedEntropy_le t hw hnonempty palette hubs bounded
  have htree := entropy_le_root hw (by simpa only [StoredTree.erase_pool] using hnonempty)
  rw [StoredTree.erase_pool] at htree
  have hbudget := AsymptoticRates.two_type_budget_le T t.pool.members.card (promotions t.erase) X K
    hT hX hnT hprom hmass hK
  have hKnonneg : 0 ≤ K := Nat.cast_nonneg _
  have hPnonneg : (0 : ℝ) ≤ promotions t.erase := Nat.cast_nonneg _
  change K + selectedEntropy t hubs ≤ 256 * T
  change entropy t.erase ≤ T at htree
  change selectedEntropy t hubs ≤ entropy t.erase + promotions t.erase + X * Real.log 8 at he
  linarith

end SortingAdversary.Optimal.TreePriceBudget
