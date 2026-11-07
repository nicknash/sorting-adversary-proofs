import SortingAdversary.Optimal.WeakMaps
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact finite local laws and choices from approximate probabilities

The local counting engine retains the old unary lists and the raw rows whose
endpoints both lie in a selected set of labels.  This file defines that finite
law and proves the comparison guarantee from explicit absolute-error bounds.
For the manuscript's application, the supplied lists must already be the
original propagated floors and ceilings.  Computing those lists while retaining
the sparse generating graph is a separate preprocessing obligation.

The restriction of a full feasible map is locally feasible.  Its distribution
need not be the uniform local law: no approximation claim follows merely from
restriction.  The spatial-mixing estimate of the manuscript is an outstanding
proof obligation and is represented here by plainly stated error hypotheses.

`weakProbability` uses exhaustive finite enumeration.  It is executable, but
is a reference semantics rather than the manuscript's efficient ideal-state
dynamic program.  No polynomial-time guarantee is asserted for this enumerator.
-/

namespace SortingAdversary.Optimal.LocalChoice

open WeakMaps

variable {α : Type*} {K : ℕ} [Fintype α] [DecidableEq α]

/-- Restrict the generating graph and retain each old unary list exactly. -/
def induced (S : WeakSystem α K) (T : Finset α) : WeakSystem ↥T K where
  edge u v := S.edge u.val v.val
  lower v := S.lower v.val
  upper v := S.upper v.val

/-- The restriction of a full assignment to the chosen local labels. -/
def restrictMap (T : Finset α) (f : ColorMap α K) : ColorMap ↥T K :=
  fun v => f v.val

omit [Fintype α] [DecidableEq α] in
theorem valid_restrict (S : WeakSystem α K) (T : Finset α)
    (f : ColorMap α K) (hf : S.Valid f) :
    (induced S T).Valid (restrictMap T f) := by
  constructor
  · intro v
    exact hf.1 v.val
  · intro u v huv
    exact hf.2 u.val v.val huv

theorem induced_count_pos (S : WeakSystem α K) (T : Finset α) (h : 0 < S.count) :
    0 < (induced S T).count := by
  obtain ⟨f, hf⟩ := (WeakSystem.count_pos_iff S).mp h
  exact (WeakSystem.count_pos_iff _).mpr ⟨restrictMap T f, valid_restrict S T f hf⟩

/-- The uniform weak-map probability of `a ≤ b`.  The value on an empty
model set follows the field convention `0 / 0 = 0`; theorems requiring a
probability law explicitly assume a positive parent count. -/
def weakProbability (S : WeakSystem α K) (a b : α) : ℚ :=
  ((S.addRow a b).count : ℚ) / (S.count : ℚ)

/-- Appending an unused top colour with fixed old endpoints leaves every
old weak-comparison probability exactly unchanged. -/
theorem weakProbability_enlarge (S : WeakSystem α K) (a b : α) :
    weakProbability S.enlarge a b = weakProbability S a b := by
  unfold weakProbability
  rw [← WeakSystem.enlarge_addRow, WeakSystem.count_enlarge, WeakSystem.count_enlarge]

theorem weakProbability_nonneg (S : WeakSystem α K) (a b : α) :
    0 ≤ weakProbability S a b := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem weakProbability_le_one (S : WeakSystem α K) (a b : α)
    (h : 0 < S.count) : weakProbability S a b ≤ 1 := by
  have hpos : (0 : ℚ) < S.count := by exact_mod_cast h
  apply (div_le_iff₀ hpos).mpr
  simpa only [one_mul] using
    (show ((S.addRow a b).count : ℚ) ≤ S.count by
      exact_mod_cast Finset.card_le_card (S.maps_addRow_subset a b))

/-- The two weak event probabilities sum to at least one because equality is
included in both events. -/
theorem one_le_probability_sum (S : WeakSystem α K) (a b : α)
    (h : 0 < S.count) :
    1 ≤ weakProbability S a b + weakProbability S b a := by
  have hpos : (0 : ℚ) < S.count := by exact_mod_cast h
  unfold weakProbability
  rw [← add_div]
  apply (le_div_iff₀ hpos).mpr
  simpa only [one_mul] using
    (show (S.count : ℚ) ≤ (S.addRow a b).count + (S.addRow b a).count by
      exact_mod_cast S.parent_count_le_sum a b)

/-- Choose the larger rational estimate.  All old constraints remain in the
resulting system.  Public-order safety is a separate controller obligation. -/
def chooseFromEstimates (S : WeakSystem α K) (a b : α) (p q : ℚ) : WeakSystem α K :=
  if q ≤ p then S.addRow a b else S.addRow b a

theorem chooseFromEstimates_maps_subset (S : WeakSystem α K) (a b : α) (p q : ℚ) :
    (chooseFromEstimates S a b p q).maps ⊆ S.maps := by
  unfold chooseFromEstimates
  split_ifs <;> exact S.maps_addRow_subset _ _

/-- Absolute errors of at most `ε` suffice for a retained fraction of at
least `1/2 - ε`.  This is slightly stronger than the manuscript's conservative
`1/2 - 2ε` estimate.  The error estimates are assumptions, not postulates. -/
theorem approximate_larger_branch (S : WeakSystem α K) (a b : α)
    (h : 0 < S.count) (p q ε : ℚ)
    (hp : |p - weakProbability S a b| ≤ ε)
    (hq : |q - weakProbability S b a| ≤ ε) :
    (1 / 2 : ℚ) - ε ≤
      ((chooseFromEstimates S a b p q).count : ℚ) / (S.count : ℚ) := by
  have hsum := one_le_probability_sum S a b h
  have hp' := abs_le.mp hp
  have hq' := abs_le.mp hq
  unfold chooseFromEstimates
  split_ifs with hchoose
  · change (1 / 2 : ℚ) - ε ≤ weakProbability S a b
    linarith
  · change (1 / 2 : ℚ) - ε ≤ weakProbability S b a
    have hchoose' : p ≤ q := le_of_lt (lt_of_not_ge hchoose)
    linarith

theorem approximate_larger_branch_conservative (S : WeakSystem α K) (a b : α)
    (h : 0 < S.count) (p q ε : ℚ) (hε : 0 ≤ ε)
    (hp : |p - weakProbability S a b| ≤ ε)
    (hq : |q - weakProbability S b a| ≤ ε) :
    (1 / 2 : ℚ) - 2 * ε ≤
      ((chooseFromEstimates S a b p q).count : ℚ) / (S.count : ℚ) := by
  have hret := approximate_larger_branch S a b h p q ε hp hq
  linarith

theorem approximate_choice_count_pos (S : WeakSystem α K) (a b : α)
    (h : 0 < S.count) (p q ε : ℚ) (hε : ε < 1 / 2)
    (hp : |p - weakProbability S a b| ≤ ε)
    (hq : |q - weakProbability S b a| ≤ ε) :
    0 < (chooseFromEstimates S a b p q).count := by
  have hret := approximate_larger_branch S a b h p q ε hp hq
  by_contra hn
  have hz : (chooseFromEstimates S a b p q).count = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, Nat.cast_zero, zero_div] at hret
  linarith

/-- Compute both estimates in the induced local law and apply that sign to
the full raw system.  Both queried labels are explicitly in the local set. -/
def chooseLocal (S : WeakSystem α K) (T : Finset α) (a b : ↥T) : WeakSystem α K :=
  chooseFromEstimates S a.val b.val
    (weakProbability (induced S T) a b) (weakProbability (induced S T) b a)

/-- The exact missing link to spatial mixing: once both local/full errors
have been bounded, the chosen global weak branch retains nearly half. -/
theorem local_choice_retains (S : WeakSystem α K) (T : Finset α) (a b : ↥T)
    (h : 0 < S.count) (ε : ℚ)
    (hab : |weakProbability (induced S T) a b - weakProbability S a.val b.val| ≤ ε)
    (hba : |weakProbability (induced S T) b a - weakProbability S b.val a.val| ≤ ε) :
    (1 / 2 : ℚ) - ε ≤ ((chooseLocal S T a b).count : ℚ) / (S.count : ℚ) := by
  exact approximate_larger_branch S a.val b.val h _ _ ε hab hba

theorem local_choice_count_pos (S : WeakSystem α K) (T : Finset α) (a b : ↥T)
    (h : 0 < S.count) (ε : ℚ) (hε : ε < 1 / 2)
    (hab : |weakProbability (induced S T) a b - weakProbability S a.val b.val| ≤ ε)
    (hba : |weakProbability (induced S T) b a - weakProbability S b.val a.val| ≤ ε) :
    0 < (chooseLocal S T a b).count := by
  exact approximate_choice_count_pos S a.val b.val h _ _ ε hε hab hba

end SortingAdversary.Optimal.LocalChoice
