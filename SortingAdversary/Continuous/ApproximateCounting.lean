import SortingAdversary.Continuous.Rates
import SortingAdversary.Basic

/-!
# The finite approximate-counting implication

This is the branch-retention algebra in Appendix H.4. The two approximations
are explicit rational inputs with explicit relative-error hypotheses. No
counting approximation algorithm, let alone an FPTAS, is assumed to exist by
an axiom or hidden in a final-bound field. A supplied algorithm satisfying
these hypotheses can be substituted into the proved finite iteration.
-/

namespace SortingAdversary.Continuous.ApproximateCounting

open Filter
open scoped Topology

def RelativeEstimate (η count : ℝ) (estimate : ℚ) : Prop :=
  (1 - η) * count ≤ (estimate : ℝ) ∧ (estimate : ℝ) ≤ (1 + η) * count

/-- Ties between the rational estimates are resolved deterministically. -/
def choose (left right : ℚ) : Answer := if right ≤ left then .less else .greater

def chosenCount (a b : ℝ) (left right : ℚ) : ℝ := if right ≤ left then a else b

noncomputable def retained (η : ℝ) : ℝ := (1 - η) / 2

noncomputable def loss (η : ℝ) : ℝ := 1 - log2 (1 - η)

theorem retained_pos {η : ℝ} (hη : η < 1) : 0 < retained η := by
  unfold retained
  positivity

theorem retained_le_one {η : ℝ} (hη : 0 ≤ η) : retained η ≤ 1 := by
  unfold retained
  linarith

/-- Choosing the larger estimate retains at least `(1-η)/2` of the true
combined count, with both multiplicative errors accounted for. -/
theorem chosenCount_lower {η a b : ℝ} (left right : ℚ)
    (hl : RelativeEstimate η a left) (hr : RelativeEstimate η b right) :
    retained η * (a + b) ≤ chosenCount a b left right := by
  by_cases he : right ≤ left
  · have hc : (right : ℝ) ≤ left := by exact_mod_cast he
    have h := hr.1.trans (hc.trans hl.2)
    simp only [chosenCount, if_pos he, retained]
    nlinarith
  · have hc : (left : ℝ) ≤ right := by exact_mod_cast (le_of_not_ge he)
    have h := hl.1.trans (hc.trans hr.2)
    simp only [chosenCount, if_neg he, retained]
    nlinarith

theorem chosenCount_pos {η a b : ℝ} (hη : η < 1) (hab : 0 < a + b)
    (left right : ℚ) (hl : RelativeEstimate η a left) (hr : RelativeEstimate η b right) :
    0 < chosenCount a b left right :=
  (mul_pos (retained_pos hη) hab).trans_le (chosenCount_lower left right hl hr)

theorem determined_retention {η count : ℝ} (hη : 0 ≤ η) (hc : 0 ≤ count) :
    retained η * count ≤ count := by
  simpa using mul_le_mul_of_nonneg_right (retained_le_one hη) hc

theorem cumulative_retention (count : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r) (q : ℕ)
    (hstep : ∀ i < q, r * count i ≤ count (i + 1)) :
    count 0 * r ^ q ≤ count q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hp := ih (fun i hi => hstep i (by omega))
    calc
      count 0 * r ^ (q + 1) = r * (count 0 * r ^ q) := by rw [pow_succ]; ring
      _ ≤ r * count q := mul_le_mul_of_nonneg_left hp hr
      _ ≤ count (q + 1) := hstep q (by omega)

/-- Iterating the actual larger-estimate choice gives the manuscript's
retained-count formula. The branch-sum and chosen-branch equations are
displayed explicitly, so no probability or counting oracle is implicit. -/
theorem estimated_counts_retained {η : ℝ} (hη : η < 1)
    (count a b : ℕ → ℝ) (left right : ℕ → ℚ) (q : ℕ)
    (hsplit : ∀ i < q, count i = a i + b i)
    (hchosen : ∀ i < q, count (i + 1) = chosenCount (a i) (b i) (left i) (right i))
    (hleft : ∀ i < q, RelativeEstimate η (a i) (left i))
    (hright : ∀ i < q, RelativeEstimate η (b i) (right i)) :
    count 0 * retained η ^ q ≤ count q := by
  apply cumulative_retention count (retained η) (retained_pos hη).le q
  intro i hi
  rw [hsplit i hi, hchosen i hi]
  exact chosenCount_lower (left i) (right i) (hleft i hi) (hright i hi)

theorem loss_eq_neg_log {η : ℝ} (hη : η < 1) : loss η = -log2 (retained η) := by
  unfold loss retained
  rw [log2_div (by linarith) (by norm_num), log2_two]
  ring

theorem loss_pos {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) : 0 < loss η := by
  have hl := log2_nonpos (by linarith : 0 < 1 - η) (by linarith : 1 - η ≤ 1)
  unfold loss
  linarith

/-- A terminal singleton yields the advertised finite comparison bound. -/
theorem comparison_lower {η initial terminal : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hi : 0 < initial) (q : ℕ) (hretained : initial * retained η ^ q ≤ terminal)
    (hterminal : terminal ≤ 1) : log2 initial / loss η ≤ q := by
  have hr := retained_pos hη1
  have hp : 0 < initial * retained η ^ q := mul_pos hi (pow_pos hr q)
  have hlog := log2_mono hp (hretained.trans hterminal)
  rw [log2_mul hi.ne' (pow_pos hr q).ne', log2_pow, log2_one] at hlog
  have heq := loss_eq_neg_log hη1
  apply (div_le_iff₀ (loss_pos hη0 hη1)).mpr
  nlinarith

theorem inverse_size_comparison_lower {n : ℕ} (hn : 2 ≤ n)
    {initial terminal : ℝ} (hi : 0 < initial) (q : ℕ)
    (hretained : initial * ((1 - 1 / (n : ℝ)) / 2) ^ q ≤ terminal)
    (hterminal : terminal ≤ 1) :
    log2 initial / (1 - log2 (1 - 1 / (n : ℝ))) ≤ q := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact comparison_lower (by positivity) ((div_lt_one (by linarith)).mpr hnR)
    hi q hretained hterminal

/-- The coefficient in the conditional counting-based adversary tends to
one for the paper's choice `η=1/n`. -/
theorem reciprocal_loss_tendsto :
    Tendsto (fun n : ℕ => 1 / (1 - log2 (1 - 1 / (n : ℝ)))) atTop (𝓝 1) := by
  have hs : Tendsto (fun n : ℕ => stopCost n) atTop (𝓝 0) :=
    stopCost_tendsto.comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => 1 + stopCost n) atTop (𝓝 1) := by
    simpa only [add_zero] using hs.const_add 1
  have hh : Tendsto (fun n : ℕ => 1 / (1 + stopCost n)) atTop (𝓝 (1 / 1 : ℝ)) :=
    tendsto_const_nhds.div hd (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [one_div_one, stopCost, stopMass, sub_eq_add_neg] using hh

end SortingAdversary.Continuous.ApproximateCounting
