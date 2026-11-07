import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Finset.Max

/-!
# Rational calibration from decreasing adjacent ratios

This file contains the finite scalar argument.  The companion
`MarginalCalibration` module proves its ratio hypothesis for the actual
weak-map fibres by a reversible component-swap injection.
-/

namespace SortingAdversary.Optimal.DiscreteCalibration

open Finset

/-- The cross-product form works with zero masses and requires no division. -/
def DecreasingRatios (p : ℕ → ℚ) : Prop :=
  ∀ a b, a ≤ b → p a * p (b + 1) ≤ p (a + 1) * p b

/-- Exclusive cdf sum: `cdf p k = Pr(X < k)` for a probability law. -/
def cdf (p : ℕ → ℚ) (k : ℕ) : ℚ := ∑ i ∈ range k, p i

@[simp] theorem cdf_zero (p : ℕ → ℚ) : cdf p 0 = 0 := by simp [cdf]

theorem cdf_succ (p : ℕ → ℚ) (k : ℕ) :
    cdf p (k + 1) = cdf p k + p k := by simp [cdf, sum_range_succ]

theorem cdf_nonneg {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i) (k : ℕ) :
    0 ≤ cdf p k := sum_nonneg (fun i _ => hp i)

theorem cdf_mono {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i) : Monotone (cdf p) := by
  intro a b hab
  apply sum_le_sum_of_subset_of_nonneg (range_mono hab)
  intro i _ _
  exact hp i

/-- Summing the decreasing adjacent-ratio inequalities gives the reverse
hazard inequality for consecutive cumulative probabilities. -/
theorem mass_mul_cdf_le {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) (k : ℕ) :
    p (k + 1) * cdf p k ≤ p k * cdf p (k + 1) := by
  have hsum : p (k + 1) * cdf p k ≤ p k * (∑ j ∈ range k, p (j + 1)) := by
    simp only [cdf, mul_sum]
    apply sum_le_sum
    intro j hj
    simpa only [mul_comm] using hr j k (Nat.le_of_lt (mem_range.mp hj))
  have hshift : (∑ j ∈ range k, p (j + 1)) ≤ cdf p (k + 1) := by
    have h := sum_range_succ' p k
    change cdf p (k + 1) = _ at h
    have h0 := hp 0
    linarith
  exact hsum.trans (mul_le_mul_of_nonneg_left hshift (hp k))

/-- The cumulative distribution itself is log-concave. -/
theorem cdf_logConcave {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) (k : ℕ) :
    cdf p k * cdf p (k + 2) ≤ cdf p (k + 1) ^ 2 := by
  have h := mass_mul_cdf_le hp hr k
  rw [show k + 2 = (k + 1) + 1 by omega, cdf_succ, cdf_succ]
  rw [cdf_succ] at h
  nlinarith

theorem reverse_hazard_adjacent {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) (k : ℕ) :
    p (k + 1) * cdf p (k + 1) ≤ p k * cdf p (k + 2) := by
  have h := mass_mul_cdf_le hp hr k
  have h0 := cdf_succ p k
  have h1 : cdf p (k + 2) = cdf p (k + 1) + p (k + 1) := by
    simpa only [Nat.add_assoc] using cdf_succ p (k + 1)
  simp only [h1, h0] at h ⊢
  nlinarith

/-- Reverse hazards decrease throughout any interval with a positive first
CDF.  No positivity assumption is imposed on individual interior masses. -/
theorem reverse_hazard {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) {a i : ℕ} (hai : a ≤ i)
    (ha : 0 < cdf p (a + 1)) :
    p i * cdf p (a + 1) ≤ p a * cdf p (i + 1) := by
  induction i, hai using Nat.le_induction with
  | base => rfl
  | succ i hai ih =>
    have hFi : 0 < cdf p (i + 1) :=
      ha.trans_le (cdf_mono hp (Nat.add_le_add_right hai 1))
    have hadj := reverse_hazard_adjacent hp hr i
    apply le_of_mul_le_mul_right (a := cdf p (i + 1)) _ hFi
    calc
      (p (i + 1) * cdf p (a + 1)) * cdf p (i + 1) =
          (p (i + 1) * cdf p (i + 1)) * cdf p (a + 1) := by ring
      _ ≤ (p i * cdf p (i + 2)) * cdf p (a + 1) :=
        mul_le_mul_of_nonneg_right hadj ha.le
      _ = (p i * cdf p (a + 1)) * cdf p (i + 2) := by ring
      _ ≤ (p a * cdf p (i + 1)) * cdf p (i + 2) :=
        mul_le_mul_of_nonneg_right ih (cdf_nonneg hp _)
      _ = (p a * cdf p (i + 1 + 1)) * cdf p (i + 1) := by ring

/-- The lower endpoint estimate uses only cumulative brackets.  Summing the
reverse hazard bound gives the stronger constant `9/128` before weakening to
the manuscript's `1/16`. -/
theorem lower_endpoint {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) {N a b : ℕ} (htotal : cdf p N = 1)
    (hab : a ≤ b) (hbN : b < N)
    (ha : (3 / 16 : ℚ) ≤ cdf p (a + 1))
    (hprev : cdf p a ≤ (5 / 16 : ℚ))
    (hb : (11 / 16 : ℚ) ≤ cdf p (b + 1)) :
    1 / (16 * (b + 1 - a : ℕ) : ℚ) ≤ p a := by
  have hapos : 0 < cdf p (a + 1) := by linarith
  have hmass : (3 / 8 : ℚ) ≤ ∑ i ∈ Ico a (b + 1), p i := by
    rw [sum_Ico_eq_sub p (by omega : a ≤ b + 1)]
    change (3 / 8 : ℚ) ≤ cdf p (b + 1) - cdf p a
    linarith
  have hterm : ∀ i ∈ Ico a (b + 1), p i * cdf p (a + 1) ≤ p a := by
    intro i hi
    obtain ⟨hai, hib⟩ := mem_Ico.mp hi
    have h := reverse_hazard hp hr hai hapos
    have hCDF : cdf p (i + 1) ≤ 1 := by
      rw [← htotal]
      apply cdf_mono hp
      omega
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left hCDF (hp a))
  have hsum := sum_le_sum hterm
  rw [← sum_mul] at hsum
  simp only [sum_const, nsmul_eq_mul, Nat.card_Ico] at hsum
  have hprod : (3 / 8 : ℚ) * (3 / 16 : ℚ) ≤
      (∑ i ∈ Ico a (b + 1), p i) * cdf p (a + 1) :=
    mul_le_mul hmass ha (by norm_num) (by linarith)
  have hm : (0 : ℚ) < (b + 1 - a : ℕ) := by
    exact_mod_cast (show 0 < b + 1 - a by omega)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℚ) < 16) hm)).mpr
  nlinarith

/-- Reflection of a finite sequence, extended by zero beyond its palette. -/
def reverse (p : ℕ → ℚ) (N : ℕ) (i : ℕ) : ℚ := if i < N then p (N - 1 - i) else 0

theorem reverse_nonneg {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i) (N i : ℕ) :
    0 ≤ reverse p N i := by
  unfold reverse
  split_ifs
  · exact hp _
  · rfl

theorem reverse_ratios {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) (N : ℕ) : DecreasingRatios (reverse p N) := by
  intro a b hab
  by_cases hb : b + 1 < N
  · have ha : a < N := by omega
    have ha1 : a + 1 < N := by omega
    have hb0 : b < N := by omega
    simp only [reverse, if_pos ha, if_pos hb, if_pos ha1, if_pos hb0]
    have h := hr (N - 1 - (b + 1)) (N - 1 - (a + 1)) (by omega)
    have heqa : N - 1 - (a + 1) + 1 = N - 1 - a := by omega
    have heqb : N - 1 - (b + 1) + 1 = N - 1 - b := by omega
    simpa only [heqa, heqb, mul_comm] using h
  · rw [show reverse p N (b + 1) = 0 by simp [reverse, hb], mul_zero]
    exact mul_nonneg (reverse_nonneg hp _ _) (reverse_nonneg hp _ _)

theorem cdf_reverse (p : ℕ → ℚ) {N k : ℕ} (hk : k ≤ N) :
    cdf (reverse p N) k = cdf p N - cdf p (N - k) := by
  by_cases hN : N = 0
  · have hk0 : k = 0 := by omega
    simp [hN, hk0]
  · have hN1 : N - 1 + 1 = N := by omega
    calc
      cdf (reverse p N) k = ∑ j ∈ Ico 0 k, p (N - 1 - j) := by
        rw [Nat.Ico_zero_eq_range]
        apply sum_congr rfl
        intro i hi
        simp [reverse, (Nat.lt_of_lt_of_le (mem_range.mp hi) hk)]
      _ = ∑ j ∈ Ico (N - k) N, p j := by
        simpa only [hN1, Nat.sub_zero] using
          (sum_Ico_reflect p 0 (m := k) (n := N - 1) (by omega))
      _ = cdf p N - cdf p (N - k) := sum_Ico_eq_sub p (Nat.sub_le N k)

/-- Reflecting the same lower-endpoint argument controls the upper endpoint. -/
theorem upper_endpoint {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) {N a b : ℕ} (htotal : cdf p N = 1)
    (hab : a ≤ b) (hbN : b < N)
    (hprev : cdf p a ≤ (5 / 16 : ℚ))
    (hb : (11 / 16 : ℚ) ≤ cdf p (b + 1))
    (hbprev : cdf p b ≤ (13 / 16 : ℚ)) :
    1 / (16 * (b + 1 - a : ℕ) : ℚ) ≤ p b := by
  let a' := N - 1 - b
  let b' := N - 1 - a
  have ha'N : a' < N := by dsimp [a']; omega
  have hb'N : b' < N := by dsimp [b']; omega
  have hab' : a' ≤ b' := by dsimp [a', b']; omega
  have htotal' : cdf (reverse p N) N = 1 := by
    rw [cdf_reverse p le_rfl, Nat.sub_self, cdf_zero, sub_zero, htotal]
  have ha' : (3 / 16 : ℚ) ≤ cdf (reverse p N) (a' + 1) := by
    rw [cdf_reverse p (by omega), htotal]
    have heq : N - (a' + 1) = b := by dsimp [a']; omega
    rw [heq]
    linarith
  have hprev' : cdf (reverse p N) a' ≤ (5 / 16 : ℚ) := by
    rw [cdf_reverse p ha'N.le, htotal]
    have heq : N - a' = b + 1 := by dsimp [a']; omega
    rw [heq]
    linarith
  have hb' : (11 / 16 : ℚ) ≤ cdf (reverse p N) (b' + 1) := by
    rw [cdf_reverse p (by omega), htotal]
    have heq : N - (b' + 1) = a := by dsimp [b']; omega
    rw [heq]
    linarith
  have h := lower_endpoint (reverse_nonneg hp N) (reverse_ratios hp hr N)
    htotal' hab' hb'N ha' hprev' hb'
  have hwidth : b' + 1 - a' = b + 1 - a := by dsimp [a', b']; omega
  have hrev : reverse p N a' = p b := by
    have heq : N - 1 - a' = b := by dsimp [a']; omega
    simp [reverse, ha'N, heq]
  simpa only [hwidth, hrev] using h

private theorem le_of_steps (p : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b)
    (hs : ∀ j, a ≤ j → j < b → p j ≤ p (j + 1)) : p a ≤ p b := by
  revert hs
  induction b, hab using Nat.le_induction with
  | base => intro _; rfl
  | succ b hab ih =>
    intro hs
    have hprev := ih (fun j haj hjb => hs j haj (by omega))
    exact hprev.trans (hs b hab (Nat.lt_succ_self b))

private theorem ge_of_steps (p : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b)
    (hs : ∀ j, a ≤ j → j < b → p (j + 1) ≤ p j) : p b ≤ p a := by
  have h := le_of_steps (fun i => -p i) hab (by
    intro j haj hjb
    exact neg_le_neg (hs j haj hjb))
  linarith

/-- Decreasing adjacent ratios forbid an interior valley, including valleys
containing zero.  The endpoint minimum therefore controls the whole interval. -/
theorem min_endpoints_le {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) {a b i : ℕ} (hai : a ≤ i) (hib : i ≤ b) :
    min (p a) (p b) ≤ p i := by
  by_cases haiMass : p a ≤ p i
  · exact le_trans (min_le_left (p a) (p b)) haiMass
  · have hdrop : ∃ j, a ≤ j ∧ j < i ∧ p (j + 1) < p j := by
      by_contra h
      apply haiMass
      apply le_of_steps p hai
      intro j haj hji
      by_contra hle
      exact h ⟨j, haj, hji, lt_of_not_ge hle⟩
    obtain ⟨j, _, hji, hdrop⟩ := hdrop
    have hpj : 0 < p j := (hp (j + 1)).trans_lt hdrop
    have hdesc : ∀ k, j ≤ k → p (k + 1) ≤ p k := by
      intro k hjk
      apply le_of_mul_le_mul_left (a := p j) _ hpj
      exact (hr j k hjk).trans (mul_le_mul_of_nonneg_right hdrop.le (hp k))
    have hright : p b ≤ p i := ge_of_steps p hib (fun k hik _ => hdesc k (by omega))
    exact le_trans (min_le_right (p a) (p b)) hright

/-- Noisy quartile brackets imply the true mass lower bound at every colour
in the selected interval, including singleton intervals and both endpoints. -/
theorem calibrated_interval {p : ℕ → ℚ} (hp : ∀ i, 0 ≤ p i)
    (hr : DecreasingRatios p) {N a b : ℕ} (htotal : cdf p N = 1)
    (hab : a ≤ b) (hbN : b < N)
    (ha : (3 / 16 : ℚ) ≤ cdf p (a + 1))
    (hprev : cdf p a ≤ (5 / 16 : ℚ))
    (hb : (11 / 16 : ℚ) ≤ cdf p (b + 1))
    (hbprev : cdf p b ≤ (13 / 16 : ℚ))
    (i : ℕ) (hai : a ≤ i) (hib : i ≤ b) :
    1 / (16 * (b + 1 - a : ℕ) : ℚ) ≤ p i := by
  have hleft := lower_endpoint hp hr htotal hab hbN ha hprev hb
  have hright := upper_endpoint hp hr htotal hab hbN hprev hb hbprev
  exact (le_min hleft hright).trans (min_endpoints_le hp hr hai hib)

/-- Reported crossings in an explicitly finite palette. -/
def crossings {K : ℕ} (q : Fin (K + 1) → ℚ) (t : ℚ) : Finset (Fin (K + 1)) :=
  univ.filter (fun i => t ≤ q i)

/-- Executable first crossing.  The top-endpoint hypothesis certifies that
the search succeeds; it is erased from the computation. -/
def firstCrossing {K : ℕ} (q : Fin (K + 1) → ℚ) (t : ℚ)
    (htop : t ≤ q (Fin.last K)) : Fin (K + 1) :=
  (crossings q t).min' ⟨Fin.last K, by simp [crossings, htop]⟩

theorem firstCrossing_ge {K : ℕ} (q : Fin (K + 1) → ℚ) (t : ℚ)
    (htop : t ≤ q (Fin.last K)) : t ≤ q (firstCrossing q t htop) := by
  have hmem : firstCrossing q t htop ∈ crossings q t := min'_mem _ _
  exact (mem_filter.mp hmem).2

theorem before_firstCrossing {K : ℕ} (q : Fin (K + 1) → ℚ) (t : ℚ)
    (htop : t ≤ q (Fin.last K)) (j : Fin (K + 1))
    (hj : j < firstCrossing q t htop) : q j < t := by
  by_contra h
  have hmem : j ∈ crossings q t := by simp [crossings, le_of_not_gt h]
  have hmin : firstCrossing q t htop ≤ j := min'_le _ _ hmem
  exact (not_le_of_gt hj) hmin

theorem firstCrossing_mono_threshold {K : ℕ} (q : Fin (K + 1) → ℚ)
    {t u : ℚ} (htop : t ≤ q (Fin.last K)) (hutop : u ≤ q (Fin.last K))
    (htu : t ≤ u) : firstCrossing q t htop ≤ firstCrossing q u hutop := by
  apply min'_le
  simp only [crossings, mem_filter, mem_univ, true_and]
  exact htu.trans (firstCrossing_ge q u hutop)

theorem firstCrossing_brackets {K : ℕ} {p : ℕ → ℚ}
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf p (i.val + 1)| ≤ (1 / 16 : ℚ))
    (t : ℚ) (ht : 0 ≤ t) (htop : t ≤ q (Fin.last K)) :
    t - 1 / 16 ≤ cdf p ((firstCrossing q t htop).val + 1) ∧
      cdf p (firstCrossing q t htop).val ≤ t + 1 / 16 := by
  let c := firstCrossing q t htop
  have hc := firstCrossing_ge q t htop
  have he := abs_le.mp (herr c)
  constructor
  · change t - 1 / 16 ≤ cdf p (c.val + 1)
    change t ≤ q c at hc
    linarith
  · change cdf p c.val ≤ t + 1 / 16
    by_cases hc0 : c.val = 0
    · rw [hc0, cdf_zero]
      linarith
    · let j : Fin (K + 1) := ⟨c.val - 1, by have := c.isLt; omega⟩
      have hj : j < c := by
        change c.val - 1 < c.val
        omega
      have hbefore := before_firstCrossing q t htop j hj
      have hej := abs_le.mp (herr j)
      have hval : j.val + 1 = c.val := by dsimp [j]; omega
      rw [hval] at hej
      linarith

theorem top_crosses {K : ℕ} {p : ℕ → ℚ} (htotal : cdf p (K + 1) = 1)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf p (i.val + 1)| ≤ (1 / 16 : ℚ)) :
    (3 / 4 : ℚ) ≤ q (Fin.last K) := by
  have h := abs_le.mp (herr (Fin.last K))
  simp only [Fin.val_last, htotal] at h
  linarith

/-- The reported quarter and three-quarter first crossings.  Monotonicity
of the reported values is unnecessary for this finite first-crossing rule. -/
def quartiles {K : ℕ} (q : Fin (K + 1) → ℚ) (htop : (3 / 4 : ℚ) ≤ q (Fin.last K)) :
    Fin (K + 1) × Fin (K + 1) :=
  (firstCrossing q (1 / 4) (le_trans (by norm_num) htop), firstCrossing q (3 / 4) htop)

theorem quartiles_ordered {K : ℕ} (q : Fin (K + 1) → ℚ)
    (htop : (3 / 4 : ℚ) ≤ q (Fin.last K)) :
    (quartiles q htop).1 ≤ (quartiles q htop).2 := by
  exact firstCrossing_mono_threshold q (le_trans (by norm_num) htop) htop (by norm_num)

/-- The executable noisy-CDF choice has the true `1/(16m)` mass guarantee.
The ratio hypothesis is supplied by the weak-map injection in the companion
module, rather than by a numerical check of the reported CDF. -/
theorem noisy_quartiles {K : ℕ} {p : ℕ → ℚ}
    (hp : ∀ i, 0 ≤ p i) (hr : DecreasingRatios p) (htotal : cdf p (K + 1) = 1)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - cdf p (i.val + 1)| ≤ (1 / 16 : ℚ)) :
    let I := quartiles q (top_crosses htotal q herr)
    I.1 ≤ I.2 ∧ ∀ i : ℕ, I.1.val ≤ i → i ≤ I.2.val →
      1 / (16 * (I.2.val + 1 - I.1.val : ℕ) : ℚ) ≤ p i := by
  let htop := top_crosses htotal q herr
  let I := quartiles q htop
  have horder := quartiles_ordered q htop
  have hlo := firstCrossing_brackets q herr (1 / 4) (by norm_num)
    (le_trans (by norm_num : (1 / 4 : ℚ) ≤ 3 / 4) htop)
  have hhi := firstCrossing_brackets q herr (3 / 4) (by norm_num) htop
  change I.1 ≤ I.2 ∧ _
  refine ⟨horder, ?_⟩
  intro i hai hib
  norm_num at hlo hhi
  exact calibrated_interval hp hr htotal horder I.2.isLt hlo.1 hlo.2 hhi.1 hhi.2 i hai hib

end SortingAdversary.Optimal.DiscreteCalibration
