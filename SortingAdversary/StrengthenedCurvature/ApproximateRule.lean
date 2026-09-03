import SortingAdversary.StrengthenedCurvature.EfficientOneComparison
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# Deterministic approximate evaluation

Section 10 of the curvature notes implements the adversary by approximating
the two child potentials and choosing the smaller approximation.  This file
formalizes the numerical robustness of that decision.  The estimates are
rational, so the comparison itself is executable and deterministic.

The separate bit-complexity claim that the estimates can be produced in
polynomial time uses standard deterministic convex optimization; the semantic
comparison-tree model in this repository intentionally has no machine-cost
notion in which to state that theorem.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- A rational approximation oracle for the volumetric potential, together
with a uniform absolute error certificate. -/
structure RationalPotentialOracle (n : ℕ) where
  estimate : History n → ℚ
  error : ℝ
  error_nonneg : 0 ≤ error
  accurate : ∀ h : History n,
    |(estimate h : ℝ) - historyPotential h| ≤ error

/-- Compare the two rational child estimates. -/
def approximateChildAnswer (oracle : RationalPotentialOracle n)
    (h : History n) (q : Query n) : Answer :=
  if oracle.estimate (answerHistory h q .less) ≤
      oracle.estimate (answerHistory h q .greater) then .less else .greater

/-- Choosing the smaller approximation loses at most twice the oracle error
relative to the genuinely smaller child. -/
theorem approximateChildAnswer_le_min_add
    (oracle : RationalPotentialOracle n) (h : History n) (q : Query n) :
    historyPotential (answerHistory h q (approximateChildAnswer oracle h q)) ≤
      min (historyPotential (answerHistory h q .less))
          (historyPotential (answerHistory h q .greater)) + 2 * oracle.error := by
  have hL := abs_le.mp (oracle.accurate (answerHistory h q .less))
  have hR := abs_le.mp (oracle.accurate (answerHistory h q .greater))
  by_cases hhat : oracle.estimate (answerHistory h q .less) ≤
      oracle.estimate (answerHistory h q .greater)
  · rw [approximateChildAnswer, if_pos hhat]
    have hhatR : (oracle.estimate (answerHistory h q .less) : ℝ) ≤
        oracle.estimate (answerHistory h q .greater) := by exact_mod_cast hhat
    by_cases hLR : historyPotential (answerHistory h q .less) ≤
        historyPotential (answerHistory h q .greater)
    · rw [min_eq_left hLR]
      linarith
    · rw [min_eq_right (le_of_not_ge hLR)]
      linarith
  · rw [approximateChildAnswer, if_neg hhat]
    have hhatL : (oracle.estimate (answerHistory h q .greater) : ℝ) ≤
        oracle.estimate (answerHistory h q .less) := by
      exact_mod_cast (le_of_not_ge hhat)
    by_cases hLR : historyPotential (answerHistory h q .less) ≤
        historyPotential (answerHistory h q .greater)
    · rw [min_eq_left hLR]
      linarith
    · rw [min_eq_right (le_of_not_ge hLR)]
      linarith

/-- The additional combinatorial promise needed by approximate child
selection: both orientations of an informative query remain feasible. -/
structure InformativeApproximationOracle (n : ℕ)
    extends RationalPotentialOracle n where
  bothFeasible : ∀ (h : History n) (q : Query n), Feasible h →
    ¬(Knowledge.ofHistory h).rel q.left q.right →
    ¬(Knowledge.ofHistory h).rel q.right q.left →
    Feasible (answerHistory h q .less) ∧
      Feasible (answerHistory h q .greater)

/-- The deterministic rational-oracle implementation of the local curvature
rule.  Its per-informative-query budget is the exact geometric budget plus
twice the requested approximation accuracy. -/
noncomputable def approximateInformativeRule
    (oracle : InformativeApproximationOracle n) : InformativePotentialRule n where
  potential := historyPotential
  maxIncrease := strengthenedComparisonBudget + 2 * oracle.error
  maxIncrease_nonneg := add_nonneg strengthenedComparisonBudget_nonneg
    (mul_nonneg (by norm_num) oracle.error_nonneg)
  informativeStep := by
    intro h q hh hless hgreater
    let a := approximateChildAnswer oracle.toRationalPotentialOracle h q
    have hboth := oracle.bothFeasible h q hh hless hgreater
    have hfeasible : Feasible (answerHistory h q a) := by
      dsimp only [a, approximateChildAnswer]
      split
      · exact hboth.1
      · exact hboth.2
    obtain ⟨w, _, hw⟩ :=
      (efficientInformativeRule n).informativeStep h q hh hless hgreater
    have hmin :
        min (historyPotential (answerHistory h q .less))
            (historyPotential (answerHistory h q .greater)) -
              historyPotential h ≤ strengthenedComparisonBudget := by
      cases w with
      | less => exact (sub_le_sub_right (min_le_left _ _) _).trans hw
      | greater => exact (sub_le_sub_right (min_le_right _ _) _).trans hw
    have hchosen := approximateChildAnswer_le_min_add
      oracle.toRationalPotentialOracle h q
    refine ⟨a, hfeasible, ?_⟩
    dsimp only [a]
    linarith

/-- Complete rule for arbitrary queries; entailed queries are answered without
changing the retained geometric state. -/
noncomputable def approximatePotentialRule
    (oracle : InformativeApproximationOracle n) : PotentialRule n :=
  (approximateInformativeRule oracle).toPotentialRule

end StrengthenedCurvature
end SortingAdversary
