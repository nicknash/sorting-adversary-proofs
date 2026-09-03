import SortingAdversary.StrengthenedCurvature.ScalarEnvelope
import Mathlib.Analysis.Convex.Jensen

/-!
# Sign-separated endpoint reduction

This file contains the dimension-free summation step in equations (49)--(56)
of the strengthened-curvature note.  Once `rho` is known to lie below its two
endpoints on each sign interval, the entire row frame is summarized by the
single positive-energy parameter `r`.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem phiAverage_eq_rho_mul_sq {delta a b lambda x : ℝ} (hx : x ≠ 0) :
    phiAverage delta a b lambda x = rho delta a b lambda x * x ^ 2 := by
  simp [rho, hx]

@[simp] theorem phiAverage_zero (delta a b lambda : ℝ) :
    phiAverage delta a b lambda 0 = 0 := by
  simp [phiAverage, phiPlus, phiMinus]

theorem rho_le_positiveEndpointMax_of_convex
    {delta r a b lambda x : ℝ}
    (hr : 0 ≤ r)
    (hconv : ConvexOn ℝ (Set.Icc 0 (Real.sqrt r))
      (rho delta a b lambda))
    (hx0 : 0 ≤ x) (hxr : x ≤ Real.sqrt r) :
    rho delta a b lambda x ≤ positiveEndpointMax delta r a b lambda := by
  exact hconv.le_max_of_mem_Icc (x := 0) (y := Real.sqrt r) (z := x)
    (by simp) (by simp) ⟨hx0, hxr⟩

theorem rho_le_negativeEndpointMax_of_convex
    {delta r a b lambda x : ℝ}
    (hr : r ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc (-Real.sqrt (1 - r)) 0)
      (rho delta a b lambda))
    (hxr : -Real.sqrt (1 - r) ≤ x) (hx0 : x ≤ 0) :
    rho delta a b lambda x ≤ negativeEndpointMax delta r a b lambda := by
  have h := hconv.le_max_of_mem_Icc
    (x := -Real.sqrt (1 - r)) (y := 0) (z := x)
    (by simp) (by simp) ⟨hxr, hx0⟩
  simpa [negativeEndpointMax, max_comm] using h

/-- Equation (54): sign-separated convexity turns an arbitrary normalized
motion family into the two scalar endpoint maxima. -/
theorem normalizedMotions_frame_reduction
    (motion : NormalizedMotions ι) (delta a b lambda : ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ x → x ≤ Real.sqrt motion.positiveEnergy →
      rho delta a b lambda x ≤
        positiveEndpointMax delta motion.positiveEnergy a b lambda)
    (hneg : ∀ x : ℝ,
      -Real.sqrt (1 - motion.positiveEnergy) ≤ x → x ≤ 0 →
      rho delta a b lambda x ≤
        negativeEndpointMax delta motion.positiveEnergy a b lambda) :
    (∑ i, phiAverage delta a b lambda (motion.alpha i)) ≤
      motion.positiveEnergy *
          positiveEndpointMax delta motion.positiveEnergy a b lambda +
        (1 - motion.positiveEnergy) *
          negativeEndpointMax delta motion.positiveEnergy a b lambda := by
  let MP := positiveEndpointMax delta motion.positiveEnergy a b lambda
  let MN := negativeEndpointMax delta motion.positiveEnergy a b lambda
  have hpoint (i : ι) :
      phiAverage delta a b lambda (motion.alpha i) ≤
        (if 0 < motion.alpha i then motion.alpha i ^ 2 * MP
          else if motion.alpha i < 0 then motion.alpha i ^ 2 * MN else 0) := by
    by_cases hi0 : motion.alpha i = 0
    · simp [hi0]
    · by_cases hip : 0 < motion.alpha i
      · simp only [hip, if_pos]
        rw [phiAverage_eq_rho_mul_sq hi0, mul_comm]
        exact mul_le_mul_of_nonneg_left
          (hpos _ hip.le (motion.alpha_le_sqrt_positiveEnergy hip))
          (sq_nonneg _)
      · have hin : motion.alpha i < 0 := lt_of_le_of_ne (le_of_not_gt hip) hi0
        simp only [hip, if_false, hin, if_pos]
        rw [phiAverage_eq_rho_mul_sq hi0, mul_comm]
        have hbound : -Real.sqrt (1 - motion.positiveEnergy) ≤ motion.alpha i := by
          rw [← motion.negativeEnergy_eq]
          linarith [motion.neg_alpha_le_sqrt_negativeEnergy hin]
        exact mul_le_mul_of_nonneg_left (hneg _ hbound hin.le) (sq_nonneg _)
  calc
    (∑ i, phiAverage delta a b lambda (motion.alpha i)) ≤
        ∑ i, (if 0 < motion.alpha i then motion.alpha i ^ 2 * MP
          else if motion.alpha i < 0 then motion.alpha i ^ 2 * MN else 0) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = motion.positiveEnergy * MP + motion.negativeEnergy * MN := by
      rw [NormalizedMotions.positiveEnergy, NormalizedMotions.negativeEnergy]
      simp only [Finset.sum_filter]
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hip : 0 < motion.alpha i
      · have hin : ¬ motion.alpha i < 0 := not_lt_of_ge hip.le
        simp [hip, hin]
      · by_cases hin : motion.alpha i < 0 <;> simp [hip, hin]
    _ = motion.positiveEnergy * MP +
        (1 - motion.positiveEnergy) * MN := by
      rw [motion.negativeEnergy_eq]

end StrengthenedCurvature
end SortingAdversary
