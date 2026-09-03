import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Kernel-verified directed rational intervals

The external certificate generator works with directed multiprecision
intervals.  The trusted replay instead uses exact rational endpoints and the
theorems in this file.  Transcendental endpoints are justified by mathlib's
Taylor remainder theorem for `log`; square-root endpoints are checked by
squaring.  No floating-point operation appears in these definitions.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

/-- A closed interval with exact rational endpoints. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

namespace RationalInterval

/-- A real number is enclosed by a rational interval. -/
def Contains (I : RationalInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

/-- The exact singleton interval. -/
def point (q : ℚ) : RationalInterval := ⟨q, q⟩

/-- Directed interval addition. -/
def add (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

/-- Directed interval subtraction. -/
def sub (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower - J.upper, I.upper - J.lower⟩

/-- Directed interval negation. -/
def neg (I : RationalInterval) : RationalInterval :=
  ⟨-I.upper, -I.lower⟩

/-- The minimum of four rational endpoints. -/
def min4 (a b c d : ℚ) : ℚ := min (min a b) (min c d)

/-- The maximum of four rational endpoints. -/
def max4 (a b c d : ℚ) : ℚ := max (max a b) (max c d)

/-- General directed interval multiplication. -/
def mul (I J : RationalInterval) : RationalInterval :=
  ⟨min4 (I.lower * J.lower) (I.lower * J.upper)
      (I.upper * J.lower) (I.upper * J.upper),
    max4 (I.lower * J.lower) (I.lower * J.upper)
      (I.upper * J.lower) (I.upper * J.upper)⟩

/-- Directed interval maximum. -/
def maximum (I J : RationalInterval) : RationalInterval :=
  ⟨max I.lower J.lower, max I.upper J.upper⟩

/-- Directed multiplication when both input intervals are nonnegative. -/
def nonnegativeMul (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower * J.lower, I.upper * J.upper⟩

/-- Directed reciprocal when the input interval is strictly positive. -/
def positiveReciprocal (I : RationalInterval) : RationalInterval :=
  ⟨1 / I.upper, 1 / I.lower⟩

@[simp] theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := by
  simp [Contains, point]

theorem Contains.add {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  constructor
  · simpa [Contains, RationalInterval.add] using add_le_add hx.1 hy.1
  · simpa [Contains, RationalInterval.add] using add_le_add hx.2 hy.2

theorem Contains.sub {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.sub J).Contains (x - y) := by
  constructor
  · simpa [Contains, RationalInterval.sub] using sub_le_sub hx.1 hy.2
  · simpa [Contains, RationalInterval.sub] using sub_le_sub hx.2 hy.1

theorem Contains.neg {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  constructor
  · simpa [Contains, RationalInterval.neg] using neg_le_neg hx.2
  · simpa [Contains, RationalInterval.neg] using neg_le_neg hx.1

private theorem cast_min4 (a b c d : ℚ) :
    ((min4 a b c d : ℚ) : ℝ) =
      min (min (a : ℝ) b) (min (c : ℝ) d) := by
  simp [min4]

private theorem cast_max4 (a b c d : ℚ) :
    ((max4 a b c d : ℚ) : ℝ) =
      max (max (a : ℝ) b) (max (c : ℝ) d) := by
  simp [max4]

theorem Contains.mul {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : I.mul J |>.Contains (x * y) := by
  let il : ℝ := I.lower
  let iu : ℝ := I.upper
  let jl : ℝ := J.lower
  let ju : ℝ := J.upper
  have hxmin : min (min (il * jl) (il * ju)) (min (iu * jl) (iu * ju)) ≤ x * y := by
    by_cases hy0 : 0 ≤ y
    · have hxy : il * y ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      by_cases hil : 0 ≤ il
      · exact (min_le_of_left_le (min_le_left _ _)).trans
          ((mul_le_mul_of_nonneg_left hy.1 hil).trans hxy)
      · exact (min_le_of_left_le (min_le_right _ _)).trans
          ((mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hil)).trans hxy)
    · have hxy : iu * y ≤ x * y :=
        mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
      by_cases hiu : 0 ≤ iu
      · exact (min_le_of_right_le (min_le_left _ _)).trans
          ((mul_le_mul_of_nonneg_left hy.1 hiu).trans hxy)
      · exact (min_le_of_right_le (min_le_right _ _)).trans
          ((mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hiu)).trans hxy)
  have hxmax : x * y ≤ max (max (il * jl) (il * ju)) (max (iu * jl) (iu * ju)) := by
    by_cases hy0 : 0 ≤ y
    · have hxy : x * y ≤ iu * y := mul_le_mul_of_nonneg_right hx.2 hy0
      by_cases hiu : 0 ≤ iu
      · exact hxy.trans ((mul_le_mul_of_nonneg_left hy.2 hiu).trans
          ((le_max_right _ _).trans (le_max_right _ _)))
      · exact hxy.trans ((mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hiu)).trans
          ((le_max_left _ _).trans (le_max_right _ _)))
    · have hxy : x * y ≤ il * y :=
        mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)
      by_cases hil : 0 ≤ il
      · exact hxy.trans ((mul_le_mul_of_nonneg_left hy.2 hil).trans
          ((le_max_right _ _).trans (le_max_left _ _)))
      · exact hxy.trans ((mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hil)).trans
          ((le_max_left _ _).trans (le_max_left _ _)))
  constructor
  · simpa [Contains, RationalInterval.mul, cast_min4, il, iu, jl, ju] using hxmin
  · simpa [Contains, RationalInterval.mul, cast_max4, il, iu, jl, ju] using hxmax

theorem Contains.maximum {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.maximum J).Contains (max x y) := by
  constructor
  · simp only [Contains, RationalInterval.maximum, Rat.cast_max]
    exact max_le_max hx.1 hy.1
  · simp only [Contains, RationalInterval.maximum, Rat.cast_max]
    exact max_le_max hx.2 hy.2

theorem Contains.nonnegativeMul {I J : RationalInterval} {x y : ℝ}
    (hI : 0 ≤ I.lower) (hJ : 0 ≤ J.lower)
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.nonnegativeMul J).Contains (x * y) := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast hI) hx.1
  have hy0 : 0 ≤ y := le_trans (by exact_mod_cast hJ) hy.1
  have hIupper : 0 ≤ (I.upper : ℝ) := hx0.trans hx.2
  constructor
  · simpa [Contains, RationalInterval.nonnegativeMul] using
      mul_le_mul hx.1 hy.1 (by exact_mod_cast hJ) hx0
  · simpa [Contains, RationalInterval.nonnegativeMul] using mul_le_mul hx.2 hy.2 hy0 hIupper

theorem Contains.positiveReciprocal {I : RationalInterval} {x : ℝ}
    (hI : 0 < I.lower) (hx : I.Contains x) :
    I.positiveReciprocal.Contains (1 / x) := by
  have hlo : (0 : ℝ) < I.lower := by exact_mod_cast hI
  have hx0 : 0 < x := hlo.trans_le hx.1
  have hhi : (0 : ℝ) < I.upper := hx0.trans_le hx.2
  constructor
  · simpa [Contains, RationalInterval.positiveReciprocal] using
      one_div_le_one_div_of_le hx0 hx.2
  · simpa [Contains, RationalInterval.positiveReciprocal] using
      one_div_le_one_div_of_le hlo hx.1

/-- Rational conditions which certify an enclosure of the square root of
every nonnegative member of `I`. -/
def SqrtCertificate (I J : RationalInterval) : Prop :=
  0 ≤ I.lower ∧ 0 ≤ J.lower ∧ J.lower ^ 2 ≤ I.lower ∧
    I.upper ≤ J.upper ^ 2 ∧ 0 ≤ J.upper

theorem Contains.sqrt {I J : RationalInterval} {x : ℝ}
    (hx : I.Contains x) (hcert : SqrtCertificate I J) :
    J.Contains (Real.sqrt x) := by
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast hcert.1) hx.1
  constructor
  · apply (Real.le_sqrt (by exact_mod_cast hcert.2.1) hx0).2
    calc
      ((J.lower : ℝ) ^ 2) ≤ (I.lower : ℝ) := by exact_mod_cast hcert.2.2.1
      _ ≤ x := hx.1
  · apply (Real.sqrt_le_iff).2
    constructor
    · exact_mod_cast hcert.2.2.2.2
    · calc
        x ≤ (I.upper : ℝ) := hx.2
        _ ≤ (J.upper : ℝ) ^ 2 := by exact_mod_cast hcert.2.2.2.1

/-- The odd Taylor polynomial for `artanh`, retained as an exact rational. -/
def atanhPartial (terms : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range terms, q ^ (2 * i + 1) / (2 * i + 1)

/-- Lower endpoint for `log ((1+q)/(1-q))`. -/
def logRatioLower (terms : ℕ) (q : ℚ) : ℚ :=
  2 * atanhPartial terms q

/-- Upper endpoint for `log ((1+q)/(1-q))`. -/
def logRatioUpper (terms : ℕ) (q : ℚ) : ℚ :=
  2 * (atanhPartial terms q + q ^ (2 * terms + 1) / (1 - q ^ 2))

private theorem cast_atanhPartial (terms : ℕ) (q : ℚ) :
    ((atanhPartial terms q : ℚ) : ℝ) =
      ∑ i ∈ Finset.range terms,
        (q : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  simp [atanhPartial]

/-- Sound exact-rational bounds for a positive logarithm ratio.  Taking
`q = (x-1)/(x+1)` covers every rational `x ≥ 1`. -/
theorem log_ratio_mem (terms : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (logRatioLower terms q : ℝ) ≤
        Real.log ((1 + (q : ℝ)) / (1 - (q : ℝ))) ∧
      Real.log ((1 + (q : ℝ)) / (1 - (q : ℝ))) ≤
        (logRatioUpper terms q : ℝ) := by
  have hq0r : (0 : ℝ) ≤ q := by exact_mod_cast hq0
  have hq1r : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hlower := Real.sum_range_le_log_div hq0r hq1r terms
  have hupper := Real.log_div_le_sum_range_add hq0r hq1r terms
  rw [← cast_atanhPartial] at hlower hupper
  constructor
  · norm_num [logRatioLower]
    linarith
  · norm_num [logRatioUpper]
    linarith

/-- Rewrite a rational `x ≥ 1` into the stable `artanh` logarithm ratio. -/
theorem ratio_of_logParameter (x : ℚ) (hx : 0 < x) :
    let q := (x - 1) / (x + 1)
    ((1 + (q : ℚ)) / (1 - q) : ℚ) = x := by
  dsimp
  field_simp
  nlinarith

/-- A directly checkable logarithm enclosure for any rational `x ≥ 1`. -/
theorem log_rational_mem (terms : ℕ) (x : ℚ) (hx : 1 ≤ x) :
    let q := (x - 1) / (x + 1)
    (logRatioLower terms q : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ (logRatioUpper terms q : ℝ) := by
  dsimp
  let q : ℚ := (x - 1) / (x + 1)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hden : 0 < x + 1 := by linarith
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.2 hx) hden.le
  have hq1 : q < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio := log_ratio_mem terms q hq0 hq1
  have heqQ : (1 + q) / (1 - q) = x := ratio_of_logParameter x hx0
  have heqR : (1 + (q : ℝ)) / (1 - (q : ℝ)) = (x : ℝ) := by
    exact_mod_cast heqQ
  rw [heqR] at hratio
  simpa [q] using hratio

/-- Lower logarithm bound for an arbitrary positive rational, using
reciprocity below one. -/
def logRationalLower (terms : ℕ) (x : ℚ) : ℚ :=
  if 1 ≤ x then
    logRatioLower terms ((x - 1) / (x + 1))
  else
    -logRatioUpper terms (((1 / x) - 1) / ((1 / x) + 1))

/-- Upper logarithm bound for an arbitrary positive rational. -/
def logRationalUpper (terms : ℕ) (x : ℚ) : ℚ :=
  if 1 ≤ x then
    logRatioUpper terms ((x - 1) / (x + 1))
  else
    -logRatioLower terms (((1 / x) - 1) / ((1 / x) + 1))

theorem log_rational_mem_pos (terms : ℕ) (x : ℚ) (hx : 0 < x) :
    (logRationalLower terms x : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ (logRationalUpper terms x : ℝ) := by
  by_cases hxone : 1 ≤ x
  · simpa [logRationalLower, logRationalUpper, hxone] using
      log_rational_mem terms x hxone
  · have hxlt : x < 1 := lt_of_not_ge hxone
    have hinv : 1 ≤ 1 / x := by
      rw [one_le_div (by exact_mod_cast hx)]
      exact hxlt.le
    have hbounds := log_rational_mem terms (1 / x) hinv
    have hxr : (0 : ℝ) < x := by exact_mod_cast hx
    have hlog : Real.log ((1 / x : ℚ) : ℝ) = -Real.log (x : ℝ) := by
      rw [Rat.cast_div, Rat.cast_one, one_div, Real.log_inv]
    rw [hlog] at hbounds
    constructor
    · simp only [logRationalLower, if_neg hxone, Rat.cast_neg]
      linarith [hbounds.2]
    · simp only [logRationalUpper, if_neg hxone, Rat.cast_neg]
      linarith [hbounds.1]

/-- Directed logarithm of a strictly positive interval. -/
def logarithm (terms : ℕ) (I : RationalInterval) : RationalInterval :=
  ⟨logRationalLower terms I.lower, logRationalUpper terms I.upper⟩

theorem Contains.logarithm {I : RationalInterval} {x : ℝ}
    (terms : ℕ) (hI : 0 < I.lower) (hx : I.Contains x) :
    (I.logarithm terms).Contains (Real.log x) := by
  have hlower := log_rational_mem_pos terms I.lower hI
  have hxpos : 0 < x := (by exact_mod_cast hI : (0 : ℝ) < I.lower).trans_le hx.1
  have hupperpos : 0 < I.upper := by
    exact_mod_cast hxpos.trans_le hx.2
  have hupper := log_rational_mem_pos terms I.upper hupperpos
  constructor
  · exact hlower.1.trans
      (Real.strictMonoOn_log.monotoneOn
        (show (I.lower : ℝ) ∈ Set.Ioi 0 by
          simpa only [Set.mem_Ioi] using (show (0 : ℝ) < I.lower by exact_mod_cast hI))
        (show x ∈ Set.Ioi 0 from hxpos) hx.1)
  · exact (Real.strictMonoOn_log.monotoneOn
      (show x ∈ Set.Ioi 0 from hxpos)
      (show (I.upper : ℝ) ∈ Set.Ioi 0 by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < I.upper by exact_mod_cast hupperpos)) hx.2).trans hupper.2

end RationalInterval
end StrengthenedCurvature
end SortingAdversary
