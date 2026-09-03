import SortingAdversary.AsymptoticStatement
import SortingAdversary.Strategy
import SortingAdversary.StrengthenedCurvature.DirectedInterval

/-!
# Source specification for the sign-imbalance adversary

This module freezes the exact theorem proved in
*A Sign-Imbalance Strengthened Volumetric History Adversary for Comparison
Sorting* (Nash, 29 August 2026).

The determinant-ratio certificate is the rational number 347 / 50. Since
the potential is one half of a base-two logarithm, the resulting leading
constant is exactly 2 / log₂ (347 / 50).

In particular, the source theorem does **not** prove the formerly advertised
constant 18 / 25.
-/

namespace SortingAdversary

/-- The exact certified determinant ratio from Theorem 9.1 of the source. -/
noncomputable def strengthenedDeterminantRatio : ℝ := 347 / 50

/-- The exact leading constant 2 / log₂(347/50). -/
noncomputable def strengthenedCurvatureConstant : ℝ :=
  2 * Real.log 2 / Real.log strengthenedDeterminantRatio

/-- One uniform family of adversarial strategies forces a leading constant.

This strengthens HasLeadingConstant: the hard path is generated online by a
single history-dependent strategy for each input size, and every generated
transcript is required to have a concrete compatible ranking.

Polynomial running time of the numerical implementation is a separate
bit-complexity statement; it is not silently identified with Lean
computability here.
-/
def HasAdversaryLeadingConstant (c : ℝ) : Prop :=
  ∃ strategy : ∀ n : ℕ, Strategy n,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ t : DecisionTree n, t.Correct →
      (∃ π : Ranking n,
        Compatible π (t.run (strategy n) []).observations) ∧
      c * nLog2n n - C * n ≤ ((t.run (strategy n) []).comparisons : ℝ)

/-- The exact source-backed target for the completed development. -/
def StrengthenedCurvatureTarget : Prop :=
  HasAdversaryLeadingConstant strengthenedCurvatureConstant

/-- Forgetting the online witness recovers the ordinary decision-tree lower
bound stated by HasLeadingConstant. -/
theorem hasLeadingConstant_of_hasAdversaryLeadingConstant
    {c : ℝ} (h : HasAdversaryLeadingConstant c) :
    HasLeadingConstant c := by
  rcases h with ⟨strategy, C, hC, hforce⟩
  refine ⟨C, hC, ?_⟩
  intro n hn t ht
  rcases hforce n hn t ht with ⟨⟨π, hcompat⟩, hcost⟩
  refine ⟨π, ?_⟩
  have hrun :=
    t.run_matches_compatible_ranking (strategy n) [] π hcompat
  rw [hrun.2]
  exact hcost

/-- The certified constant is strictly below the superseded clean target
`18/25`; this comparison is proved from exact Taylor enclosures, not a decimal
evaluation. -/
theorem strengthenedCurvatureConstant_lt_eighteen_twentyfive :
    strengthenedCurvatureConstant < (18 : ℝ) / 25 := by
  let qTwo : ℚ := ((2 : ℚ) - 1) / (2 + 1)
  let qRatio : ℚ := (((347 : ℚ) / 50) - 1) / ((347 / 50) + 1)
  have htwo := StrengthenedCurvature.RationalInterval.log_rational_mem 20 (2 : ℚ)
    (by norm_num)
  have hratio := StrengthenedCurvature.RationalInterval.log_rational_mem 100
    ((347 : ℚ) / 50) (by norm_num)
  have hseparate :
      (50 : ℝ) * StrengthenedCurvature.RationalInterval.logRatioUpper 20 qTwo <
        18 * StrengthenedCurvature.RationalInterval.logRatioLower 100 qRatio := by
    norm_num [qTwo, qRatio, StrengthenedCurvature.RationalInterval.logRatioUpper,
      StrengthenedCurvature.RationalInterval.logRatioLower,
      StrengthenedCurvature.RationalInterval.atanhPartial]
  have hlogs : (50 : ℝ) * Real.log 2 <
      18 * Real.log strengthenedDeterminantRatio := by
    have hleft :
        (50 : ℝ) * Real.log 2 ≤
          50 * StrengthenedCurvature.RationalInterval.logRatioUpper 20 qTwo := by
      exact mul_le_mul_of_nonneg_left htwo.2 (by norm_num)
    have hright :
        18 * StrengthenedCurvature.RationalInterval.logRatioLower 100 qRatio ≤
          (18 : ℝ) * Real.log strengthenedDeterminantRatio := by
      simpa [strengthenedDeterminantRatio, qRatio] using
        mul_le_mul_of_nonneg_left hratio.1 (by norm_num : (0 : ℝ) ≤ 18)
    exact hleft.trans_lt (hseparate.trans_le hright)
  rw [strengthenedCurvatureConstant]
  apply (div_lt_iff₀ (Real.log_pos (by norm_num [strengthenedDeterminantRatio]))).2
  nlinarith

/-- The strengthened certificate also gives a strict improvement over the
clean coefficient `5/7`. -/
theorem five_sevenths_lt_strengthenedCurvatureConstant :
    (5 : ℝ) / 7 < strengthenedCurvatureConstant := by
  let qTwo : ℚ := ((2 : ℚ) - 1) / (2 + 1)
  let qRatio : ℚ := (((347 : ℚ) / 50) - 1) / ((347 / 50) + 1)
  have htwo := StrengthenedCurvature.RationalInterval.log_rational_mem 20 (2 : ℚ)
    (by norm_num)
  have hratio := StrengthenedCurvature.RationalInterval.log_rational_mem 100
    ((347 : ℚ) / 50) (by norm_num)
  have hseparate :
      (5 : ℝ) * StrengthenedCurvature.RationalInterval.logRatioUpper 100 qRatio <
        14 * StrengthenedCurvature.RationalInterval.logRatioLower 20 qTwo := by
    norm_num [qTwo, qRatio, StrengthenedCurvature.RationalInterval.logRatioUpper,
      StrengthenedCurvature.RationalInterval.logRatioLower,
      StrengthenedCurvature.RationalInterval.atanhPartial]
  have hlogs : (5 : ℝ) * Real.log strengthenedDeterminantRatio <
      14 * Real.log 2 := by
    have hleft :
        (5 : ℝ) * Real.log strengthenedDeterminantRatio ≤
          5 * StrengthenedCurvature.RationalInterval.logRatioUpper 100 qRatio := by
      simpa [strengthenedDeterminantRatio, qRatio] using
        mul_le_mul_of_nonneg_left hratio.2 (by norm_num : (0 : ℝ) ≤ 5)
    have hright :
        14 * StrengthenedCurvature.RationalInterval.logRatioLower 20 qTwo ≤
          (14 : ℝ) * Real.log 2 := by
      exact mul_le_mul_of_nonneg_left htwo.1 (by norm_num)
    exact hleft.trans_lt (hseparate.trans_le hright)
  rw [strengthenedCurvatureConstant]
  apply (lt_div_iff₀ (Real.log_pos (by norm_num [strengthenedDeterminantRatio]))).2
  nlinarith

end SortingAdversary
