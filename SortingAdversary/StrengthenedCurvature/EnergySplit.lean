import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive/negative electrical energy split

This file isolates the finite scalar information retained after whitening.
It formalizes equation (36) and the pointwise bounds used in equations
(37)--(39), independently of the later interval certificate.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A normalized family of electrical row motions. -/
structure NormalizedMotions (ι : Type*) [Fintype ι] where
  alpha : ι → ℝ
  energy_one : ∑ i, alpha i ^ 2 = 1

namespace NormalizedMotions

/-- Squared energy on positive motions. -/
noncomputable def positiveEnergy (motion : NormalizedMotions ι) : ℝ :=
  ∑ i with 0 < motion.alpha i, motion.alpha i ^ 2

/-- Squared energy on negative motions. -/
noncomputable def negativeEnergy (motion : NormalizedMotions ι) : ℝ :=
  ∑ i with motion.alpha i < 0, motion.alpha i ^ 2

omit [DecidableEq ι] in
theorem positiveEnergy_nonneg (motion : NormalizedMotions ι) :
    0 ≤ motion.positiveEnergy := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
theorem negativeEnergy_nonneg (motion : NormalizedMotions ι) :
    0 ≤ motion.negativeEnergy := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem positive_add_negative (motion : NormalizedMotions ι) :
    motion.positiveEnergy + motion.negativeEnergy = 1 := by
  rw [positiveEnergy, negativeEnergy, ← motion.energy_one]
  rw [← Finset.sum_union]
  · apply Finset.sum_subset
    · simp
    · intro i _ hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or] at hi
      have : motion.alpha i = 0 := le_antisymm (not_lt.1 hi.1) (not_lt.1 hi.2)
      simp [this]
  · simp only [Finset.disjoint_filter]
    intro i hpos hneg
    linarith

theorem positiveEnergy_le_one (motion : NormalizedMotions ι) :
    motion.positiveEnergy ≤ 1 := by
  rw [← motion.positive_add_negative]
  exact le_add_of_nonneg_right motion.negativeEnergy_nonneg

theorem negativeEnergy_eq (motion : NormalizedMotions ι) :
    motion.negativeEnergy = 1 - motion.positiveEnergy := by
  linarith [motion.positive_add_negative]

omit [DecidableEq ι] in
theorem alpha_sq_le_positiveEnergy (motion : NormalizedMotions ι) {i : ι}
    (hi : 0 < motion.alpha i) :
    motion.alpha i ^ 2 ≤ motion.positiveEnergy := by
  rw [positiveEnergy]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (motion.alpha j)) (by simp [hi])

omit [DecidableEq ι] in
theorem alpha_sq_le_negativeEnergy (motion : NormalizedMotions ι) {i : ι}
    (hi : motion.alpha i < 0) :
    motion.alpha i ^ 2 ≤ motion.negativeEnergy := by
  rw [negativeEnergy]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (motion.alpha j)) (by simp [hi])

/-- Every positive motion is at most the square root of the positive energy. -/
theorem alpha_le_sqrt_positiveEnergy (motion : NormalizedMotions ι) {i : ι}
    (hi : 0 < motion.alpha i) :
    motion.alpha i ≤ Real.sqrt motion.positiveEnergy := by
  calc
    motion.alpha i = |motion.alpha i| := (abs_of_pos hi).symm
    _ = Real.sqrt (motion.alpha i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt motion.positiveEnergy :=
      Real.sqrt_le_sqrt (motion.alpha_sq_le_positiveEnergy hi)

/-- The magnitude of every negative motion is at most the square root of the
negative energy. -/
theorem neg_alpha_le_sqrt_negativeEnergy (motion : NormalizedMotions ι) {i : ι}
    (hi : motion.alpha i < 0) :
    -motion.alpha i ≤ Real.sqrt motion.negativeEnergy := by
  calc
    -motion.alpha i = |motion.alpha i| := (abs_of_neg hi).symm
    _ = Real.sqrt (motion.alpha i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt motion.negativeEnergy :=
      Real.sqrt_le_sqrt (motion.alpha_sq_le_negativeEnergy hi)

end NormalizedMotions
end StrengthenedCurvature
end SortingAdversary
