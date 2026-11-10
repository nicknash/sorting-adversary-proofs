import SortingAdversary.Continuous.Weights

/-!
# The continuous manuscript's refinement and prefix accounting

The objects below are finite lists of actual numeric gains and anchor levels.
The theorems derive the global estimates from the individual tariffs, answer
losses, and the arc budget.  Connecting these lists to the executable tree's
volumes is a separate semantic obligation: no such connection is assumed by
definition or hidden in a field containing the desired final bound.
-/

namespace SortingAdversary.Continuous

open scoped BigOperators

noncomputable def answerRetained (k : ℝ) : ℝ := 1 / 2 - 1 / (100 * k)
noncomputable def answerLoss (k : ℝ) : ℝ := -log2 (answerRetained k)

theorem answerRetained_bounds {k : ℝ} (hk : 64 ≤ k) :
    3 / 8 ≤ answerRetained k ∧ answerRetained k ≤ 1 / 2 := by
  have hk0 : 0 < k := by linarith
  have hinv : 0 < 1 / (100 * k) := by positivity
  have hsmall : 1 / (100 * k) ≤ 1 / 8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  unfold answerRetained
  constructor <;> linarith

theorem answerLoss_bounds {k : ℝ} (hk : 64 ≤ k) :
    1 ≤ answerLoss k ∧ answerLoss k ≤ 3 / 2 := by
  have hb := answerRetained_bounds hk
  have hp : 0 < answerRetained k := by linarith
  have hhalf : log2 (1 / 2) = -1 := by
    rw [log2_div (by norm_num) (by norm_num), log2_one, log2_two]
    ring
  have hlo := log2_mono hp hb.2
  rw [hhalf] at hlo
  have hsquare : (1 / 8 : ℝ) ≤ answerRetained k ^ 2 := by nlinarith
  have hhi := log2_mono (by norm_num : (0 : ℝ) < 1 / 8) hsquare
  have hlog8 : log2 (1 / 8) = -3 := by
    have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [h8, log2_div (by norm_num) (by norm_num), log2_one, log2_pow, log2_two]
    norm_num
  rw [hlog8, log2_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hhi
  unfold answerLoss
  constructor <;> linarith

private theorem path_coefficient {k : ℝ} (hk : 64 ≤ k) :
    k / 4 ≤ stopMass k * (k - 1) / 2 - 4 := by
  have hk0 : 0 < k := by linarith
  have heq : k * stopMass k = k - 1 := by
    unfold stopMass
    field_simp
  apply (mul_le_mul_iff_right₀ hk0).mp
  nlinarith [sq_nonneg (k - 32)]

/-- Distinct dyadic anchors make a complete path batch profitable. This uses
their finite cardinality and the per-anchor tariff, not a batch-gain premise. -/
theorem path_gain_lower {k : ℕ} (hk : 64 ≤ k)
    (anchors : Finset DyadicAnchor) (gain : DyadicAnchor → ℝ)
    (hcard : anchors.card = 2 ^ k)
    (htariff : ∀ c ∈ anchors, stopMass k * c.1 - 4 ≤ gain c) :
    (k : ℝ) / 4 * anchors.card ≤ ∑ c ∈ anchors, gain c := by
  classical
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) < k := by linarith
  have hs : 0 ≤ stopMass k := (stopMass_pos hk1).le
  have hhigh := high_anchor_count (show 1 ≤ k by omega) hcard
  have hlevel : ((2 ^ (k - 1) : ℕ) : ℝ) * (k - 1 : ℕ) ≤
      ∑ c ∈ anchors, (c.1 : ℝ) := by
    have hterm : ∀ c ∈ anchors,
        (if k - 1 ≤ c.1 then ((k - 1 : ℕ) : ℝ) else 0) ≤ (c.1 : ℝ) := by
      intro c hc
      split_ifs with h
      · exact_mod_cast h
      · positivity
    have hsum := Finset.sum_le_sum hterm
    have hfiltered : (∑ c ∈ anchors,
        if k - 1 ≤ c.1 then ((k - 1 : ℕ) : ℝ) else 0) =
        ((anchors.filter (fun c => k - 1 ≤ c.1)).card : ℝ) * (k - 1 : ℕ) := by
      rw [← Finset.sum_filter]
      simp
    rw [hfiltered] at hsum
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hhigh)
      (Nat.cast_nonneg (k - 1))).trans hsum
  have hsum := Finset.sum_le_sum htariff
  have hsimpl : (∑ c ∈ anchors, (stopMass k * c.1 - 4)) =
      stopMass k * (∑ c ∈ anchors, (c.1 : ℝ)) - 4 * anchors.card := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hsimpl] at hsum
  have hpow : ((2 ^ k : ℕ) : ℝ) = 2 * ((2 ^ (k - 1) : ℕ) : ℝ) := by
    have hn : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ, Nat.mul_comm]
    exact_mod_cast hn
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hlevels := mul_le_mul_of_nonneg_left hlevel hs
  rw [hsub] at hlevels
  have hcoeff := mul_le_mul_of_nonneg_right (path_coefficient hkR)
    (show (0 : ℝ) ≤ anchors.card by positivity)
  rw [hcard, hpow] at hcoeff ⊢
  rw [hcard, hpow] at hsum
  nlinarith

/-- One of the three ways a completed comparison call refines items. A path
batch records its distinct reduced anchors and the gains at those anchors. -/
inductive RefinementEvent where
  | selection (anchor : DyadicAnchor) (gain : ℝ)
  | degree (anchor : DyadicAnchor) (gain : ℝ)
  | path (anchors : Finset DyadicAnchor) (gain : DyadicAnchor → ℝ)

namespace RefinementEvent

def count : RefinementEvent → ℕ
  | .selection _ _ => 1
  | .degree _ _ => 1
  | .path anchors _ => anchors.card

def degrees : RefinementEvent → ℕ
  | .degree _ _ => 1
  | _ => 0

noncomputable def gain : RefinementEvent → ℝ
  | .selection _ g => g
  | .degree _ g => g
  | .path anchors g => ∑ c ∈ anchors, g c

noncomputable def cost (k : ℝ) : RefinementEvent → ℝ
  | .selection c _ => anchorCost k c.1
  | .degree c _ => anchorCost k c.1
  | .path anchors _ => ∑ c ∈ anchors, anchorCost k c.1

/-- Only local gain promises occur here. Path-batch gain is derived above. -/
def Valid (k : ℕ) : RefinementEvent → Prop
  | .selection c g => (k : ℝ) < g ∧ stopMass k * c.1 - 4 ≤ g
  | .degree c g => stopMass k * c.1 - 4 ≤ g
  | .path anchors g => anchors.card = 2 ^ k ∧
      ∀ c ∈ anchors, stopMass k * c.1 - 4 ≤ g c

theorem gain_lower {k : ℕ} (hk : 64 ≤ k) (e : RefinementEvent) (he : e.Valid k) :
    (k : ℝ) / 4 * (e.count - (e.degrees : ℝ)) - 4 * e.degrees ≤ e.gain := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  cases e with
  | selection c g =>
    simp only [Valid] at he
    simp only [count, degrees, gain, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one,
      mul_zero]
    linarith [he.1]
  | degree c g =>
    simp only [Valid] at he
    have h := mul_nonneg (stopMass_pos (show (1 : ℝ) < k by linarith)).le
      (Nat.cast_nonneg c.1 : (0 : ℝ) ≤ c.1)
    simp only [count, degrees, gain, Nat.cast_one, sub_self, mul_zero, zero_sub, mul_one]
    linarith
  | path anchors g =>
    simpa [count, degrees, gain] using path_gain_lower hk anchors g he.1 he.2

theorem cost_le {k : ℕ} (hk : 64 ≤ k) (e : RefinementEvent) (he : e.Valid k) :
    e.cost k ≤ tariffSlope k * e.gain + tariffIntercept k * e.count := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  cases e with
  | selection c g =>
    simpa [cost, gain, count] using anchorCost_le_tariff hk1 c.1 he.2
  | degree c g =>
    simpa [cost, gain, count] using anchorCost_le_tariff hk1 c.1 he
  | path anchors g =>
    have hs := Finset.sum_le_sum (fun c hc => anchorCost_le_tariff hk1 c.1 (he.2 c hc))
    simpa [cost, gain, count, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
      using hs

end RefinementEvent

/-- A chronological log of completed refinement batches and answer losses. -/
structure AccountingLog where
  events : List RefinementEvent
  losses : List ℝ

namespace AccountingLog

def refinements (L : AccountingLog) : ℕ := (L.events.map RefinementEvent.count).sum
def degreeRepairs (L : AccountingLog) : ℕ := (L.events.map RefinementEvent.degrees).sum
def comparisons (L : AccountingLog) : ℕ := L.losses.length
noncomputable def totalGain (L : AccountingLog) : ℝ :=
  (L.events.map RefinementEvent.gain).sum
noncomputable def totalCost (L : AccountingLog) (k : ℝ) : ℝ :=
  (L.events.map (RefinementEvent.cost k)).sum
noncomputable def logVolume (L : AccountingLog) : ℝ := L.totalGain - L.losses.sum

theorem gain_lower {k : ℕ} (hk : 64 ≤ k) (L : AccountingLog)
    (he : ∀ e ∈ L.events, e.Valid k) :
    (k : ℝ) / 4 * (L.refinements - (L.degreeRepairs : ℝ)) -
      4 * L.degreeRepairs ≤ L.totalGain := by
  obtain ⟨events, losses⟩ := L
  induction events with
  | nil => simp [refinements, degreeRepairs, totalGain]
  | cons e es ih =>
    have h := e.gain_lower hk (he e (by simp))
    have hi := ih (fun e' he' => he e' (by simp [he']))
    simp only [refinements, degreeRepairs, totalGain, List.map_cons, List.sum_cons,
      Nat.cast_add] at hi ⊢
    linarith

theorem cost_le {k : ℕ} (hk : 64 ≤ k) (L : AccountingLog)
    (he : ∀ e ∈ L.events, e.Valid k) :
    L.totalCost k ≤ tariffSlope k * L.totalGain + tariffIntercept k * L.refinements := by
  obtain ⟨events, losses⟩ := L
  induction events with
  | nil => simp [refinements, totalGain, totalCost]
  | cons e es ih =>
    have h := e.cost_le hk (he e (by simp))
    have hi := ih (fun e' he' => he e' (by simp [he']))
    simp only [refinements, totalGain, totalCost, List.map_cons, List.sum_cons,
      Nat.cast_add] at hi ⊢
    linarith

private theorem loss_sum_bound (as : List ℝ) (b : ℝ)
    (h : ∀ a ∈ as, a ≤ b) : as.sum ≤ b * as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun a' ha' => h a' (by simp [ha']))
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem gain_le {k : ℝ} (L : AccountingLog)
    (hloss : ∀ a ∈ L.losses, a ≤ answerLoss k) :
    L.totalGain ≤ L.logVolume + answerLoss k * L.comparisons := by
  have hsum := loss_sum_bound L.losses (answerLoss k) hloss
  unfold logVolume comparisons
  linarith

/-- Lemma "Refinement count", with the paper's explicit constant `C=8`.
`harcs` is the arc budget supplied by the state-transition proof: each degree
repair removes `k` arcs and each comparison inserts at most one. -/
theorem refinement_count {k : ℕ} (hk : 64 ≤ k) (L : AccountingLog)
    (he : ∀ e ∈ L.events, e.Valid k)
    (hloss : ∀ a ∈ L.losses, a ≤ answerLoss k)
    (hvolume : L.logVolume ≤ 0)
    (harcs : k * L.degreeRepairs ≤ L.comparisons) :
    (L.refinements : ℝ) ≤ 8 * L.comparisons / k := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlow := L.gain_lower hk he
  have hupp := L.gain_le hloss
  have hanswer := mul_le_mul_of_nonneg_right (answerLoss_bounds hkR).2
    (Nat.cast_nonneg L.comparisons : (0 : ℝ) ≤ L.comparisons)
  have hd : (k : ℝ) * L.degreeRepairs ≤ L.comparisons := by exact_mod_cast harcs
  have hsmall : 16 * (L.degreeRepairs : ℝ) ≤ L.comparisons := by
    have hnonneg : (0 : ℝ) ≤ L.degreeRepairs := Nat.cast_nonneg _
    nlinarith
  apply (le_div_iff₀ hk0).mpr
  nlinarith

end AccountingLog

/-- The explicit excess in the comparison-prefix theorem (`C=8`). -/
noncomputable def prefixOverhead (k : ℝ) : ℝ :=
  tariffSlope k * answerLoss k - 1 + 2 * stopCost k +
    8 * tariffIntercept k / k

theorem prefixOverhead_nonneg {k : ℝ} (hk : 64 ≤ k) : 0 ≤ prefixOverhead k := by
  have hk1 : 1 < k := by linarith
  have ha := tariffSlope_ge_one hk1
  have hb := (answerLoss_bounds hk).1
  have hd := stopCost_nonneg hk1
  have hi := tariffIntercept_nonneg hk1
  have hprod : 1 ≤ tariffSlope k * answerLoss k := by nlinarith
  unfold prefixOverhead
  positivity

/-- The prefix estimate after inserting the sampling/packing bound.  The
premise `hpacking` is deliberately explicit: this theorem does not assert
that an arbitrary log comes from the continuous adversary's tree. -/
theorem prefix_bound_of_packing {k : ℕ} (hk : 64 ≤ k)
    (L : AccountingLog) (s : ℕ) (initialEntropy remainingEntropy : ℝ)
    (he : ∀ e ∈ L.events, e.Valid k)
    (hloss : ∀ a ∈ L.losses, a ≤ answerLoss k)
    (hvolume : L.logVolume ≤ 0)
    (harcs : k * L.degreeRepairs ≤ L.comparisons)
    (hqueried : s ≤ 2 * L.comparisons)
    (hpacking : initialEntropy - s * stopCost k + L.logVolume - L.totalCost k ≤
      remainingEntropy) :
    initialEntropy - (1 + prefixOverhead k) * L.comparisons ≤ remainingEntropy := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hcost := L.cost_le hk he
  have hgain := L.gain_le hloss
  have ha := tariffSlope_ge_one hk1
  have hd := stopCost_nonneg hk1
  have hb := tariffIntercept_nonneg hk1
  have hp := L.refinement_count hk he hloss hvolume harcs
  have hs : (s : ℝ) ≤ 2 * L.comparisons := by exact_mod_cast hqueried
  have hsd := mul_le_mul_of_nonneg_right hs hd
  have hbg := mul_le_mul_of_nonneg_left hp hb
  have hag := mul_le_mul_of_nonneg_left hgain (le_trans (by norm_num) ha)
  have hz : 0 ≤ (1 - tariffSlope k) * L.logVolume :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hvolume
  unfold prefixOverhead
  simp only [div_eq_mul_inv] at hbg ⊢
  nlinarith

end SortingAdversary.Continuous
