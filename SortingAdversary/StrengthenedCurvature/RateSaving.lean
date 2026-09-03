import SortingAdversary.StrengthenedCurvature.StrengthenedIntegration
import SortingAdversary.StrengthenedCurvature.ScalarEnvelope
import SortingAdversary.StrengthenedCurvature.FirstDerivative

/-!
# Rate-norm bounds and the integrated curvature saving

This file formalizes equations (36)--(42) of the strengthened-curvature
note.  The positive and negative parts of a normalized motion are followed
along a positive displacement, and the resulting norm gap is integrated.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open Set intervalIntegral
open scoped BigOperators

set_option maxHeartbeats 2000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace NormalizedMotions

/-- Reflection of every normalized motion. -/
noncomputable def neg (motion : NormalizedMotions ι) : NormalizedMotions ι where
  alpha i := -motion.alpha i
  energy_one := by simpa using motion.energy_one

@[simp] theorem neg_alpha (motion : NormalizedMotions ι) (i : ι) :
    motion.neg.alpha i = -motion.alpha i := rfl

@[simp] theorem positiveEnergy_neg (motion : NormalizedMotions ι) :
    motion.neg.positiveEnergy = motion.negativeEnergy := by
  unfold positiveEnergy negativeEnergy neg
  congr 1
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hi <;> linarith
  · funext i
    ring

/-- Squared norm of the positive scaled rates at time `s`. -/
noncomputable def positiveRateEnergy (motion : NormalizedMotions ι) (s : ℝ) : ℝ :=
  ∑ i with 0 < motion.alpha i,
    (motion.alpha i / (1 + s * motion.alpha i)) ^ 2

/-- Squared norm of the negative scaled rates at time `s`. -/
noncomputable def negativeRateEnergy (motion : NormalizedMotions ι) (s : ℝ) : ℝ :=
  ∑ i with motion.alpha i < 0,
    (motion.alpha i / (1 + s * motion.alpha i)) ^ 2

noncomputable def positiveRateNorm (motion : NormalizedMotions ι) (s : ℝ) : ℝ :=
  Real.sqrt (motion.positiveRateEnergy s)

noncomputable def negativeRateNorm (motion : NormalizedMotions ι) (s : ℝ) : ℝ :=
  Real.sqrt (motion.negativeRateEnergy s)

theorem alpha_sq_le_one (motion : NormalizedMotions ι) (i : ι) :
    motion.alpha i ^ 2 ≤ 1 := by
  rw [← motion.energy_one]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (motion.alpha j))
    (Finset.mem_univ i)

theorem neg_one_le_alpha (motion : NormalizedMotions ι) (i : ι) :
    -1 ≤ motion.alpha i := by
  nlinarith [motion.alpha_sq_le_one i, sq_nonneg (motion.alpha i + 1)]

theorem alpha_le_one (motion : NormalizedMotions ι) (i : ι) :
    motion.alpha i ≤ 1 := by
  nlinarith [motion.alpha_sq_le_one i, sq_nonneg (motion.alpha i - 1)]

theorem rateDenominator_pos (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (i : ι) :
    0 < 1 + s * motion.alpha i := by
  have hlow := motion.neg_one_le_alpha i
  have hsalpha : -s ≤ s * motion.alpha i := by
    nlinarith
  linarith

theorem positiveRateEnergy_nonneg (motion : NormalizedMotions ι) (s : ℝ) :
    0 ≤ motion.positiveRateEnergy s := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem negativeRateEnergy_nonneg (motion : NormalizedMotions ι) (s : ℝ) :
    0 ≤ motion.negativeRateEnergy s := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem positiveRateEnergy_zero (motion : NormalizedMotions ι) :
    motion.positiveRateEnergy 0 = motion.positiveEnergy := by
  simp [positiveRateEnergy, positiveEnergy]

@[simp] theorem negativeRateEnergy_zero (motion : NormalizedMotions ι) :
    motion.negativeRateEnergy 0 = motion.negativeEnergy := by
  simp [negativeRateEnergy, negativeEnergy]

/-- Positive rates shrink under positive displacement. -/
theorem positiveRateEnergy_le (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    motion.positiveRateEnergy s ≤ motion.positiveEnergy := by
  unfold positiveRateEnergy positiveEnergy
  apply Finset.sum_le_sum
  intro i hi
  have hai : 0 < motion.alpha i := (Finset.mem_filter.mp hi).2
  have hden : 0 < 1 + s * motion.alpha i := motion.rateDenominator_pos hs0 hs1 i
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hden)).2
  have hden1 : 1 ≤ (1 + s * motion.alpha i) ^ 2 := by
    nlinarith [mul_nonneg hs0 hai.le]
  nlinarith [sq_nonneg (motion.alpha i)]

/-- Negative rates grow under positive displacement. -/
theorem negativeEnergy_le_rateEnergy (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    motion.negativeEnergy ≤ motion.negativeRateEnergy s := by
  unfold negativeRateEnergy negativeEnergy
  apply Finset.sum_le_sum
  intro i hi
  have hai : motion.alpha i < 0 := (Finset.mem_filter.mp hi).2
  have hden : 0 < 1 + s * motion.alpha i := motion.rateDenominator_pos hs0 hs1 i
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hden)).2
  have hden1 : (1 + s * motion.alpha i) ^ 2 ≤ 1 := by
    have hupper : 1 + s * motion.alpha i ≤ 1 := by nlinarith
    nlinarith
  nlinarith [sq_nonneg (motion.alpha i)]

/-- Equation (37), positive side. -/
theorem positiveEnergy_div_le_rateEnergy (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    motion.positiveEnergy /
        (1 + s * Real.sqrt motion.positiveEnergy) ^ 2 ≤
      motion.positiveRateEnergy s := by
  unfold positiveRateEnergy positiveEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hai : 0 < motion.alpha i := (Finset.mem_filter.mp hi).2
  have hP0 : 0 ≤ Real.sqrt motion.positiveEnergy := Real.sqrt_nonneg _
  have haiP := motion.alpha_le_sqrt_positiveEnergy hai
  have hdeni : 0 < 1 + s * motion.alpha i := motion.rateDenominator_pos hs0 hs1 i
  have hdenP : 0 < 1 + s * Real.sqrt motion.positiveEnergy := by positivity
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hdenP) (sq_pos_of_pos hdeni)).2
  have hdenle : 1 + s * motion.alpha i ≤
      1 + s * Real.sqrt motion.positiveEnergy := by nlinarith
  have hsqle : (1 + s * motion.alpha i) ^ 2 ≤
      (1 + s * Real.sqrt motion.positiveEnergy) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (motion.alpha i)]

/-- Equation (37), negative side. -/
theorem negativeRateEnergy_le_div (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    motion.negativeRateEnergy s ≤
      motion.negativeEnergy /
        (1 - s * Real.sqrt motion.negativeEnergy) ^ 2 := by
  unfold negativeRateEnergy negativeEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hai : motion.alpha i < 0 := (Finset.mem_filter.mp hi).2
  let N := Real.sqrt motion.negativeEnergy
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN1 : N ≤ 1 := by
    rw [Real.sqrt_le_one]
    rw [← motion.positive_add_negative]
    exact le_add_of_nonneg_left motion.positiveEnergy_nonneg
  have hmag := motion.neg_alpha_le_sqrt_negativeEnergy hai
  have hdeni : 0 < 1 + s * motion.alpha i := motion.rateDenominator_pos hs0 hs1 i
  have hdenN : 0 < 1 - s * N := by nlinarith
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hdeni) (sq_pos_of_pos hdenN)).2
  have hdenle : 1 - s * N ≤ 1 + s * motion.alpha i := by nlinarith
  have hsqle : (1 - s * N) ^ 2 ≤ (1 + s * motion.alpha i) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (motion.alpha i)]

theorem positiveRateNorm_le_sqrt (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    motion.positiveRateNorm s ≤ Real.sqrt motion.positiveEnergy := by
  unfold positiveRateNorm
  exact Real.sqrt_le_sqrt (motion.positiveRateEnergy_le hs0 hs1)

theorem sqrt_negative_le_rateNorm (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Real.sqrt motion.negativeEnergy ≤ motion.negativeRateNorm s := by
  unfold negativeRateNorm
  exact Real.sqrt_le_sqrt (motion.negativeEnergy_le_rateEnergy hs0 hs1)

theorem sqrt_positive_div_le_rateNorm (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Real.sqrt motion.positiveEnergy /
        (1 + s * Real.sqrt motion.positiveEnergy) ≤
      motion.positiveRateNorm s := by
  let P := Real.sqrt motion.positiveEnergy
  let ps := motion.positiveRateNorm s
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hden : 0 < 1 + s * P := by positivity
  have hps0 : 0 ≤ ps := Real.sqrt_nonneg _
  have hPsq : P ^ 2 = motion.positiveEnergy :=
    Real.sq_sqrt motion.positiveEnergy_nonneg
  have hpssq : ps ^ 2 = motion.positiveRateEnergy s :=
    Real.sq_sqrt (motion.positiveRateEnergy_nonneg s)
  have henergy := motion.positiveEnergy_div_le_rateEnergy hs0 hs1
  have hsquare : (P / (1 + s * P)) ^ 2 ≤ ps ^ 2 := by
    rw [div_pow, hPsq, hpssq]
    exact henergy
  dsimp only [P, ps] at *
  nlinarith [sq_nonneg
    (Real.sqrt motion.positiveEnergy / (1 + s * Real.sqrt motion.positiveEnergy) +
      motion.positiveRateNorm s)]

theorem negativeRateNorm_le_sqrt_div (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    motion.negativeRateNorm s ≤
      Real.sqrt motion.negativeEnergy /
        (1 - s * Real.sqrt motion.negativeEnergy) := by
  let N := Real.sqrt motion.negativeEnergy
  let ns := motion.negativeRateNorm s
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN1 : N ≤ 1 := by
    rw [Real.sqrt_le_one]
    rw [← motion.positive_add_negative]
    exact le_add_of_nonneg_left motion.positiveEnergy_nonneg
  have hden : 0 < 1 - s * N := by nlinarith
  have hns0 : 0 ≤ ns := Real.sqrt_nonneg _
  have hNsq : N ^ 2 = motion.negativeEnergy :=
    Real.sq_sqrt motion.negativeEnergy_nonneg
  have hnssq : ns ^ 2 = motion.negativeRateEnergy s :=
    Real.sq_sqrt (motion.negativeRateEnergy_nonneg s)
  have henergy := motion.negativeRateEnergy_le_div hs0 hs1
  have hsquare : ns ^ 2 ≤ (N / (1 - s * N)) ^ 2 := by
    rw [div_pow, hNsq, hnssq]
    exact henergy
  dsimp only [N, ns] at *
  have hright0 : 0 ≤ Real.sqrt motion.negativeEnergy /
      (1 - s * Real.sqrt motion.negativeEnergy) := div_nonneg hN0 hden.le
  nlinarith [sq_nonneg
    (motion.negativeRateNorm s + Real.sqrt motion.negativeEnergy /
      (1 - s * Real.sqrt motion.negativeEnergy))]

/-- When negative energy dominates, the squared rate-norm gap never falls
below its initial squared gap (equation (38)). -/
theorem rateGap_sq_ge_of_sqrt_positive_le_negative
    (motion : NormalizedMotions ι) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hNP : Real.sqrt motion.positiveEnergy ≤ Real.sqrt motion.negativeEnergy) :
    (Real.sqrt motion.negativeEnergy - Real.sqrt motion.positiveEnergy) ^ 2 ≤
      (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
  have hp := motion.positiveRateNorm_le_sqrt hs0 hs1
  have hn := motion.sqrt_negative_le_rateNorm hs0 hs1
  have hleft : motion.positiveRateNorm s - motion.negativeRateNorm s ≤
      Real.sqrt motion.positiveEnergy - Real.sqrt motion.negativeEnergy := by linarith
  have hsign : motion.positiveRateNorm s - motion.negativeRateNorm s ≤ 0 := by
    linarith
  nlinarith

/-- When positive energy dominates, equation (39) in squared positive-part
form. -/
theorem positivePart_crossover_sq_le_rateGap_sq
    (motion : NormalizedMotions ι) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    positivePart
        (Real.sqrt motion.positiveEnergy /
            (1 + s * Real.sqrt motion.positiveEnergy) -
          Real.sqrt motion.negativeEnergy /
            (1 - s * Real.sqrt motion.negativeEnergy)) ^ 2 ≤
      (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
  let e := Real.sqrt motion.positiveEnergy /
      (1 + s * Real.sqrt motion.positiveEnergy) -
    Real.sqrt motion.negativeEnergy /
      (1 - s * Real.sqrt motion.negativeEnergy)
  have hp := motion.sqrt_positive_div_le_rateNorm hs0 hs1
  have hn := motion.negativeRateNorm_le_sqrt_div hs0 hs1
  have hgap : e ≤ motion.positiveRateNorm s - motion.negativeRateNorm s := by
    dsimp only [e]
    linarith
  change positivePart e ^ 2 ≤
    (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2
  rcases le_total e 0 with he | he
  · rw [positivePart, max_eq_right he]
    simpa using sq_nonneg
      (motion.positiveRateNorm s - motion.negativeRateNorm s)
  · rw [positivePart, max_eq_left he]
    nlinarith

theorem sum_positivePart_scaledRate_eq (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑ i, positivePart
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2) =
      motion.positiveRateEnergy s := by
  rw [positiveRateEnergy]
  calc
    (∑ i, positivePart
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2) =
        ∑ i, if 0 < motion.alpha i then
          (motion.alpha i / (1 + s * motion.alpha i)) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hden := motion.rateDenominator_pos hs0 hs1 i
      by_cases hpos : 0 < motion.alpha i
      · rw [if_pos hpos]
        simp [positivePart, max_eq_left (div_nonneg hpos.le hden.le)]
      · rw [if_neg hpos]
        have hnonpos : motion.alpha i ≤ 0 := le_of_not_gt hpos
        simp [positivePart,
          max_eq_right (div_nonpos_of_nonpos_of_nonneg hnonpos hden.le)]
    _ = ∑ i with 0 < motion.alpha i,
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2 := by
      rw [Finset.sum_filter]

theorem sum_negativePart_scaledRate_eq (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑ i, negativePart
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2) =
      motion.negativeRateEnergy s := by
  rw [negativeRateEnergy]
  calc
    (∑ i, negativePart
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2) =
        ∑ i, if motion.alpha i < 0 then
          (motion.alpha i / (1 + s * motion.alpha i)) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hden := motion.rateDenominator_pos hs0 hs1 i
      by_cases hneg : motion.alpha i < 0
      · rw [if_pos hneg]
        have hquot : motion.alpha i / (1 + s * motion.alpha i) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hneg.le hden.le
        simp [negativePart, max_eq_left (neg_nonneg.mpr hquot)]
      · rw [if_neg hneg]
        have hnonneg : 0 ≤ motion.alpha i := le_of_not_gt hneg
        have hquot : 0 ≤ motion.alpha i / (1 + s * motion.alpha i) :=
          div_nonneg hnonneg hden.le
        simp [negativePart, max_eq_right (neg_nonpos.mpr hquot)]
    _ = ∑ i with motion.alpha i < 0,
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2 := by
      rw [Finset.sum_filter]

theorem rateNormGap_continuousOn (motion : NormalizedMotions ι)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ContinuousOn (fun s =>
      motion.positiveRateNorm s - motion.negativeRateNorm s) (Set.Icc 0 a) := by
  have hterm (i : ι) : ContinuousOn
      (fun s => (motion.alpha i / (1 + s * motion.alpha i)) ^ 2)
      (Set.Icc (0 : ℝ) a) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
    intro s hs
    exact (motion.rateDenominator_pos hs.1 (hs.2.trans_lt ha1) i).ne'
  have hp : ContinuousOn (motion.positiveRateEnergy) (Set.Icc (0 : ℝ) a) := by
    unfold positiveRateEnergy
    exact continuousOn_finsetSum _ fun i _ => hterm i
  have hn : ContinuousOn (motion.negativeRateEnergy) (Set.Icc (0 : ℝ) a) := by
    unfold negativeRateEnergy
    exact continuousOn_finsetSum _ fun i _ => hterm i
  exact (ContinuousOn.sqrt hp).sub (ContinuousOn.sqrt hn)

theorem weighted_rateGap_intervalIntegrable (motion : NormalizedMotions ι)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    IntervalIntegrable
      (fun s => (a - s) *
        (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2)
      MeasureTheory.volume 0 a := by
  apply ContinuousOn.intervalIntegrable
  have hgap := motion.rateNormGap_continuousOn ha0 ha1
  have hcont : ContinuousOn
      (fun s => (a - s) *
        (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2)
      (Set.Icc (0 : ℝ) a) :=
    (continuousOn_const.sub continuousOn_id).mul (hgap.pow 2)
  simpa [Set.uIcc_of_le ha0] using hcont

/-- The first branch of equation (41): when negative energy dominates, the
constant initial norm gap is a lower bound throughout the displacement. -/
theorem dominantNegative_saving_le_integral (motion : NormalizedMotions ι)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hNP : Real.sqrt motion.positiveEnergy ≤ Real.sqrt motion.negativeEnergy) :
    a ^ 2 / 4 *
        (Real.sqrt motion.negativeEnergy - Real.sqrt motion.positiveEnergy) ^ 2 ≤
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..a, (a - s) *
        (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
  let c := (Real.sqrt motion.negativeEnergy -
    Real.sqrt motion.positiveEnergy) ^ 2
  have hlower : IntervalIntegrable (fun s : ℝ => (a - s) * c)
      MeasureTheory.volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hupper := motion.weighted_rateGap_intervalIntegrable ha0 ha1
  have hmono : (∫ s in (0 : ℝ)..a, (a - s) * c) ≤
      ∫ s in (0 : ℝ)..a, (a - s) *
        (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
    apply intervalIntegral.integral_mono_on ha0 hlower hupper
    intro s hs
    apply mul_le_mul_of_nonneg_left
    · exact motion.rateGap_sq_ge_of_sqrt_positive_le_negative hs.1
        (hs.2.trans_lt ha1) hNP
    · exact sub_nonneg.mpr hs.2
  have hlinear : (∫ s in (0 : ℝ)..a, (a - s)) = a ^ 2 / 2 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => a) MeasureTheory.volume 0 a :=
      intervalIntegrable_const
    have hid : IntervalIntegrable (fun s : ℝ => s) MeasureTheory.volume 0 a := by
      exact continuousOn_id.intervalIntegrable
    rw [intervalIntegral.integral_sub hconst hid]
    simp [integral_id]
    ring
  have hlowerEval : (∫ s in (0 : ℝ)..a, (a - s) * c) = a ^ 2 / 2 * c := by
    rw [intervalIntegral.integral_mul_const, hlinear]
  rw [hlowerEval] at hmono
  dsimp only [c] at hmono ⊢
  nlinarith

theorem sqrt_positive_le_one (motion : NormalizedMotions ι) :
    Real.sqrt motion.positiveEnergy ≤ 1 := by
  rw [Real.sqrt_le_one]
  exact motion.positiveEnergy_le_one

theorem sqrt_negative_le_one (motion : NormalizedMotions ι) :
    Real.sqrt motion.negativeEnergy ≤ 1 := by
  rw [Real.sqrt_le_one]
  rw [← motion.positive_add_negative]
  exact le_add_of_nonneg_left motion.positiveEnergy_nonneg

/-- The rational crossover expression is nonnegative before `s₀`. -/
theorem crossoverExpression_nonneg (motion : NormalizedMotions ι)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hPN : Real.sqrt motion.negativeEnergy < Real.sqrt motion.positiveEnergy)
    (hN : 0 < Real.sqrt motion.negativeEnergy)
    (hs : s ≤
      (Real.sqrt motion.positiveEnergy - Real.sqrt motion.negativeEnergy) /
        (2 * Real.sqrt motion.positiveEnergy *
          Real.sqrt motion.negativeEnergy)) :
    0 ≤ Real.sqrt motion.positiveEnergy /
          (1 + s * Real.sqrt motion.positiveEnergy) -
        Real.sqrt motion.negativeEnergy /
          (1 - s * Real.sqrt motion.negativeEnergy) := by
  let P := Real.sqrt motion.positiveEnergy
  let N := Real.sqrt motion.negativeEnergy
  have hP : 0 < P := hN.trans hPN
  have hN0 : 0 < N := hN
  have hN1 : N ≤ 1 := motion.sqrt_negative_le_one
  have hdenP : 0 < 1 + s * P := by positivity
  have hdenN : 0 < 1 - s * N := by nlinarith
  have hprod : s * (2 * P * N) ≤ P - N := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * P * N)).mp hs
  rw [sub_nonneg]
  apply (div_le_div_iff₀ hdenN hdenP).2
  dsimp only [P, N] at hprod ⊢
  nlinarith

theorem crossIntegrand_intervalIntegrable (motion : NormalizedMotions ι)
    {a L : ℝ} (hL0 : 0 ≤ L) (hLa : L ≤ a) (ha1 : a < 1) :
    IntervalIntegrable
      (crossIntegrand a (Real.sqrt motion.positiveEnergy)
        (Real.sqrt motion.negativeEnergy)) MeasureTheory.volume 0 L := by
  apply ContinuousOn.intervalIntegrable
  unfold crossIntegrand
  have hP0 : 0 ≤ Real.sqrt motion.positiveEnergy := Real.sqrt_nonneg _
  have hN0 : 0 ≤ Real.sqrt motion.negativeEnergy := Real.sqrt_nonneg _
  have hN1 : Real.sqrt motion.negativeEnergy ≤ 1 := motion.sqrt_negative_le_one
  apply (continuousOn_const.sub continuousOn_id).mul
  apply ContinuousOn.pow
  apply ContinuousOn.sub
  · apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL0] using hs
    have : 0 ≤ s * Real.sqrt motion.positiveEnergy :=
      mul_nonneg hs'.1 hP0
    change 1 + s * Real.sqrt motion.positiveEnergy ≠ 0
    exact ne_of_gt (by linarith)
  · apply ContinuousOn.div continuousOn_const
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL0] using hs
    have hs0 : 0 ≤ s := hs'.1
    have hsL : s ≤ L := hs'.2
    have hsa : s < 1 := lt_of_le_of_lt (hsL.trans hLa) ha1
    have hsN : s * Real.sqrt motion.negativeEnergy ≤ s * 1 :=
      mul_le_mul_of_nonneg_left hN1 hs0
    change 1 - s * Real.sqrt motion.negativeEnergy ≠ 0
    exact ne_of_gt (by linarith)

/-- The positive-energy branch of equation (41), including the `N = 0`
limit, is bounded by the integrated rate-norm gap. -/
theorem dominantPositive_saving_le_integral (motion : NormalizedMotions ι)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hPN : Real.sqrt motion.negativeEnergy < Real.sqrt motion.positiveEnergy) :
    (if Real.sqrt motion.negativeEnergy = 0 then
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..a,
          crossIntegrand a (Real.sqrt motion.positiveEnergy)
            (Real.sqrt motion.negativeEnergy) s
      else
        let s0 :=
          (Real.sqrt motion.positiveEnergy - Real.sqrt motion.negativeEnergy) /
            (2 * Real.sqrt motion.positiveEnergy *
              Real.sqrt motion.negativeEnergy)
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..min a s0,
          crossIntegrand a (Real.sqrt motion.positiveEnergy)
            (Real.sqrt motion.negativeEnergy) s) ≤
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..a, (a - s) *
        (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
  let P := Real.sqrt motion.positiveEnergy
  let N := Real.sqrt motion.negativeEnergy
  have hactual := motion.weighted_rateGap_intervalIntegrable ha0 ha1
  by_cases hNzero : N = 0
  · rw [if_pos hNzero]
    have hcross := motion.crossIntegrand_intervalIntegrable ha0 le_rfl ha1
    have hmono : (∫ s in (0 : ℝ)..a, crossIntegrand a P N s) ≤
        ∫ s in (0 : ℝ)..a, (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
      apply intervalIntegral.integral_mono_on ha0 hcross hactual
      intro s hs
      have hgap := motion.positivePart_crossover_sq_le_rateGap_sq
        hs.1 (hs.2.trans_lt ha1)
      have he0 : 0 ≤ P / (1 + s * P) - N / (1 - s * N) := by
        rw [hNzero]
        simp only [zero_div, sub_zero]
        have hP0 : 0 ≤ P := Real.sqrt_nonneg _
        have hden : 0 ≤ 1 + s * P :=
          add_nonneg zero_le_one (mul_nonneg hs.1 hP0)
        exact div_nonneg hP0 hden
      unfold crossIntegrand
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hs.2)
      simpa [P, N, positivePart, max_eq_left he0] using hgap
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  · rw [if_neg hNzero]
    let s0 := (P - N) / (2 * P * N)
    let L := min a s0
    have hNpos : 0 < N := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hNzero)
    have hPpos : 0 < P := hNpos.trans hPN
    have hs0pos : 0 < s0 := by
      dsimp only [s0]
      positivity
    have hL0 : 0 ≤ L := le_min ha0 hs0pos.le
    have hLa : L ≤ a := min_le_left _ _
    have hLs0 : L ≤ s0 := min_le_right _ _
    have hcross := motion.crossIntegrand_intervalIntegrable hL0 hLa ha1
    have hactualL : IntervalIntegrable
        (fun s => (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2)
        MeasureTheory.volume 0 L :=
      hactual.mono_set (by
        simpa [Set.uIcc_of_le ha0, Set.uIcc_of_le hL0] using
          (Set.Icc_subset_Icc_right hLa : Set.Icc (0 : ℝ) L ⊆ Set.Icc 0 a))
    have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) L,
        crossIntegrand a P N s ≤ (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
      intro s hs
      have hs1 : s < 1 := lt_of_le_of_lt (hs.2.trans hLa) ha1
      have he0 := motion.crossoverExpression_nonneg hs.1 hs1 hPN hNpos
        (hs.2.trans hLs0)
      have hgap := motion.positivePart_crossover_sq_le_rateGap_sq hs.1 hs1
      unfold crossIntegrand
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hs.2.trans hLa))
      simpa [P, N, positivePart, max_eq_left he0] using hgap
    have hmonoL : (∫ s in (0 : ℝ)..L, crossIntegrand a P N s) ≤
        ∫ s in (0 : ℝ)..L, (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 :=
      intervalIntegral.integral_mono_on hL0 hcross hactualL hpoint
    have hrestrict : (∫ s in (0 : ℝ)..L, (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2) ≤
        ∫ s in (0 : ℝ)..a, (a - s) *
          (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
      apply intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := a)
        le_rfl hL0 hLa
      · show ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) a),
          (0 : ℝ) ≤ (a - s) *
            (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg _)
      · exact hactual
    dsimp only [L, s0]
    exact mul_le_mul_of_nonneg_left (hmonoL.trans hrestrict) (by norm_num)

/-- Equation (41) in the exact form used by the scalar certificate. -/
theorem gammaPlus_le_integratedRateGap (motion : NormalizedMotions ι)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    gammaPlus a motion.positiveEnergy ≤
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..a, (a - s) *
        (motion.positiveRateNorm s - motion.negativeRateNorm s) ^ 2 := by
  rw [gammaPlus]
  dsimp only
  rw [show 1 - motion.positiveEnergy = motion.negativeEnergy by
    symm
    exact motion.negativeEnergy_eq]
  by_cases hNP : Real.sqrt motion.negativeEnergy ≥ Real.sqrt motion.positiveEnergy
  · rw [if_pos hNP]
    exact motion.dominantNegative_saving_le_integral ha0 ha1 hNP
  · rw [if_neg hNP]
    exact motion.dominantPositive_saving_le_integral ha0 ha1 (lt_of_not_ge hNP)

end NormalizedMotions

variable {n : ℕ}

/-- The generic matrix rate gap specializes exactly to the old electrical
motion rate gap; the prospective query row contributes a leading zero. -/
theorem scaledRateGap_augmented_eq {h : History n} {x : Placement n}
    (o : Observation n) (hx : InHistoryPolytope h x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    scaledRateGap (augmentedMotions h x o) s =
      (electricalNormalizedMotions h x o hx).positiveRateNorm s -
        (electricalNormalizedMotions h x o hx).negativeRateNorm s := by
  have hp := (electricalNormalizedMotions h x o hx).sum_positivePart_scaledRate_eq hs0 hs1
  have hn := (electricalNormalizedMotions h x o hx).sum_negativePart_scaledRate_eq hs0 hs1
  unfold scaledRateGap
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [scaledRate, augmentedMotions, rowDenominator, zero_mul, add_zero,
    zero_div, positivePart, negativePart, neg_zero, max_self,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  change Real.sqrt
      (∑ i, positivePart
        ((electricalNormalizedMotions h x o hx).alpha i /
          (1 + s * (electricalNormalizedMotions h x o hx).alpha i)) ^ 2) -
      Real.sqrt
        (∑ i, negativePart
          ((electricalNormalizedMotions h x o hx).alpha i /
            (1 + s * (electricalNormalizedMotions h x o hx).alpha i)) ^ 2) = _
  rw [hp, hn]
  rfl

/-- Reflected specialization used by the negative trial branch. -/
theorem scaledRateGap_neg_augmented_eq {h : History n} {x : Placement n}
    (o : Observation n) (hx : InHistoryPolytope h x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    scaledRateGap (-(augmentedMotions h x o)) s =
      (electricalNormalizedMotions h x o hx).neg.positiveRateNorm s -
        (electricalNormalizedMotions h x o hx).neg.negativeRateNorm s := by
  let motion := (electricalNormalizedMotions h x o hx).neg
  have hp := motion.sum_positivePart_scaledRate_eq hs0 hs1
  have hn := motion.sum_negativePart_scaledRate_eq hs0 hs1
  unfold scaledRateGap
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [scaledRate, Pi.neg_apply, augmentedMotions, rowDenominator,
    neg_zero, zero_mul, add_zero, zero_div, positivePart, negativePart,
    max_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  change Real.sqrt
      (∑ i, positivePart
        (motion.alpha i / (1 + s * motion.alpha i)) ^ 2) -
      Real.sqrt
        (∑ i, negativePart
          (motion.alpha i / (1 + s * motion.alpha i)) ^ 2) = _
  rw [hp, hn]
  rfl

end StrengthenedCurvature
end SortingAdversary
