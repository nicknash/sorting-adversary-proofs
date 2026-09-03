import SortingAdversary.StrengthenedCurvature.GlobalBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# A majority-compatible-rankings rule

The semantic target of this repository concerns ordinary deterministic
comparison trees.  Independently of the volumetric construction, the standard
majority adversary supplies a particularly small unconditional inhabitant of
`CertifiedRuleFamily`: answer each query with the branch containing at least
half of the rankings still compatible with the transcript.

This closes the exported source constant without adding an analytic axiom.  It
also provides a useful reference implementation against which the more
specialized volumetric rule can be audited.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

/-- All rankings compatible with a history. -/
noncomputable def compatibleRankings (h : History n) : Finset (Ranking n) := by
  classical
  exact Finset.univ.filter fun π => Compatible π h

@[simp] theorem mem_compatibleRankings {h : History n} {π : Ranking n} :
    π ∈ compatibleRankings h ↔ Compatible π h := by
  classical
  simp [compatibleRankings]

theorem compatibleRankings_nonempty_iff (h : History n) :
    (compatibleRankings h).Nonempty ↔ Feasible h := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨π, mem_compatibleRankings.mp hπ⟩
  · rintro ⟨π, hπ⟩
    exact ⟨π, mem_compatibleRankings.mpr hπ⟩

private theorem query_ranks_ne (π : Ranking n) (q : Query n) :
    π q.left ≠ π q.right := fun h => q.distinct (π.injective h)

theorem holds_greater_iff_not_holds_less (π : Ranking n) (q : Query n) :
    (Observation.mk q .greater).Holds π ↔
      ¬(Observation.mk q .less).Holds π := by
  simp only [Observation.Holds]
  constructor
  · exact fun hgt hlt => (lt_asymm hgt hlt).elim
  · intro hn
    exact lt_of_le_of_ne (le_of_not_gt hn) (query_ranks_ne π q).symm

noncomputable def lessRankings (h : History n) (q : Query n) :
    Finset (Ranking n) := by
  classical
  exact (compatibleRankings h).filter fun π =>
    (Observation.mk q .less).Holds π

noncomputable def notLessRankings (h : History n) (q : Query n) :
    Finset (Ranking n) := by
  classical
  exact (compatibleRankings h).filter fun π =>
    ¬(Observation.mk q .less).Holds π

theorem compatibleRankings_less (h : History n) (q : Query n) :
    compatibleRankings (answerHistory h q .less) =
      lessRankings h q := by
  classical
  ext π
  simp [answerHistory, lessRankings, and_comm]

theorem compatibleRankings_greater (h : History n) (q : Query n) :
    compatibleRankings (answerHistory h q .greater) =
      notLessRankings h q := by
  classical
  ext π
  simp [answerHistory, notLessRankings, and_comm,
    holds_greater_iff_not_holds_less]

theorem compatibleRankings_card_split (h : History n) (q : Query n) :
    (compatibleRankings (answerHistory h q .less)).card +
        (compatibleRankings (answerHistory h q .greater)).card =
      (compatibleRankings h).card := by
  classical
  rw [compatibleRankings_less, compatibleRankings_greater]
  simpa [lessRankings, notLessRankings] using
    (Finset.card_filter_add_card_filter_not
      (s := compatibleRankings h)
      (fun π => (Observation.mk q .less).Holds π))

/-- The branch with at least as many compatible rankings. -/
noncomputable def majorityAnswer (h : History n) (q : Query n) : Answer :=
  if (compatibleRankings (answerHistory h q .less)).card ≤
      (compatibleRankings (answerHistory h q .greater)).card then
    .greater
  else .less

theorem majorityAnswer_card (h : History n) (q : Query n) :
    (compatibleRankings h).card ≤
      2 * (compatibleRankings (answerHistory h q (majorityAnswer h q))).card := by
  classical
  have hsplit := compatibleRankings_card_split h q
  unfold majorityAnswer
  split_ifs with hle
  · omega
  · omega

theorem feasible_majorityAnswer {h : History n} (q : Query n)
    (hh : Feasible h) : Feasible (answerHistory h q (majorityAnswer h q)) := by
  rw [← compatibleRankings_nonempty_iff] at hh ⊢
  have hparent : 0 < (compatibleRankings h).card := Finset.card_pos.mpr hh
  have hcard := majorityAnswer_card h q
  apply Finset.card_pos.mp
  omega

/-- Shifted logarithmic version-space potential.  The shift makes its terminal
value exactly `n log₂ n`, while Stirling's bound keeps the initial value below
`3n/2`. -/
noncomputable def countingPotential (n : ℕ) (h : History n) : ℝ :=
  nLog2n n - Real.log (compatibleRankings h).card / Real.log 2

theorem one_le_comparisonBudget : (1 : ℝ) ≤ comparisonBudget := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hmono : Real.log (4 : ℝ) ≤ Real.log strengthenedDeterminantRatio :=
    Real.strictMonoOn_log.monotoneOn (by norm_num)
      (by norm_num [strengthenedDeterminantRatio])
      (by norm_num [strengthenedDeterminantRatio])
  rw [hfour] at hmono
  rw [comparisonBudget]
  exact (le_div_iff₀ (mul_pos (by norm_num) hlogtwo)).2 (by nlinarith)

theorem countingPotential_majority_step_one {h : History n} (q : Query n)
    (hh : Feasible h) :
    countingPotential n (answerHistory h q (majorityAnswer h q)) -
        countingPotential n h ≤ 1 := by
  let oldCard := (compatibleRankings h).card
  let newCard :=
    (compatibleRankings (answerHistory h q (majorityAnswer h q))).card
  have holdNat : 0 < oldCard := by
    exact Finset.card_pos.mpr ((compatibleRankings_nonempty_iff h).mpr hh)
  have hnewFeasible := feasible_majorityAnswer q hh
  have hnewNat : 0 < newCard := by
    exact Finset.card_pos.mpr
      ((compatibleRankings_nonempty_iff _).mpr hnewFeasible)
  have hcardNat : oldCard ≤ 2 * newCard := majorityAnswer_card h q
  have hold : (0 : ℝ) < oldCard := by exact_mod_cast holdNat
  have hnew : (0 : ℝ) < newCard := by exact_mod_cast hnewNat
  have hcard : (oldCard : ℝ) ≤ 2 * (newCard : ℝ) := by exact_mod_cast hcardNat
  have hlog : Real.log (oldCard : ℝ) ≤ Real.log (2 * (newCard : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hold (mul_pos (by norm_num) hnew) hcard
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnew.ne'] at hlog
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold countingPotential
  change nLog2n n - Real.log (newCard : ℝ) / Real.log 2 -
      (nLog2n n - Real.log (oldCard : ℝ) / Real.log 2) ≤ 1
  rw [show nLog2n n - Real.log (newCard : ℝ) / Real.log 2 -
      (nLog2n n - Real.log (oldCard : ℝ) / Real.log 2) =
    (Real.log (oldCard : ℝ) - Real.log (newCard : ℝ)) / Real.log 2 by ring]
  apply (div_le_iff₀ hlogtwo).2
  nlinarith

theorem countingPotential_majority_step {h : History n} (q : Query n)
    (hh : Feasible h) :
    countingPotential n (answerHistory h q (majorityAnswer h q)) -
        countingPotential n h ≤ comparisonBudget :=
  (countingPotential_majority_step_one q hh).trans one_le_comparisonBudget

/-- The majority version-space potential rule. -/
noncomputable def countingPotentialRule (n : ℕ) : PotentialRule n where
  potential := countingPotential n
  maxIncrease := comparisonBudget
  maxIncrease_nonneg := comparisonBudget_pos.le
  step := by
    intro h q hh
    exact ⟨majorityAnswer h q, feasible_majorityAnswer q hh,
      countingPotential_majority_step q hh⟩

/-- The same majority rule with its sharp one-bit local budget. -/
noncomputable def countingUnitPotentialRule (n : ℕ) : PotentialRule n where
  potential := countingPotential n
  maxIncrease := 1
  maxIncrease_nonneg := by norm_num
  step := by
    intro h q hh
    exact ⟨majorityAnswer h q, feasible_majorityAnswer q hh,
      countingPotential_majority_step_one q hh⟩

@[simp] theorem compatibleRankings_nil_card (n : ℕ) :
    (compatibleRankings ([] : History n)).card = n.factorial := by
  classical
  simp [compatibleRankings, Fintype.card_perm]

theorem countingPotential_initial_upper (n : ℕ) :
    countingPotential n [] ≤ (3 / 2 : ℝ) * n := by
  by_cases hn : n = 0
  · subst n
    norm_num [countingPotential, nLog2n]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlogn : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have hlogpi : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    have hstirling := Stirling.le_log_factorial_stirling hn
    have hdiff : (n : ℝ) * Real.log n - Real.log (n.factorial : ℝ) ≤ n := by
      nlinarith
    have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogtwoLower : (2 / 3 : ℝ) < Real.log 2 := by
      exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    rw [countingPotential, compatibleRankings_nil_card, nLog2n]
    have hquot :
        ((n : ℝ) * Real.log n - Real.log (n.factorial : ℝ)) / Real.log 2 ≤
          (3 / 2 : ℝ) * n := by
      apply (div_le_iff₀ hlogtwo).2
      nlinarith
    convert hquot using 1 <;> ring

theorem compatibleRankings_reverse (h : History n) :
    compatibleRankings h.reverse = compatibleRankings h := by
  classical
  ext π
  simp [Compatible, List.forall_iff_forall_mem]

theorem compatibleRankings_run_card_eq_one (rule : PotentialRule n)
    (t : DecisionTree n) (ht : t.Correct) :
    (compatibleRankings
      (t.run rule.strategy []).observations.reverse).card = 1 := by
  let result := t.run rule.strategy []
  obtain ⟨π₀, hπ₀⟩ := rule.run_consistent t
  have hnonempty : (compatibleRankings result.observations.reverse).Nonempty := by
    refine ⟨π₀, ?_⟩
    rw [mem_compatibleRankings]
    simpa [Compatible, List.forall_iff_forall_mem] using hπ₀
  have hsub : compatibleRankings result.observations.reverse ⊆ {result.output} := by
    intro π hπ
    rw [Finset.mem_singleton]
    have hcompatRev := mem_compatibleRankings.mp hπ
    have hcompat : Compatible π result.observations := by
      simpa [Compatible, List.forall_iff_forall_mem] using hcompatRev
    have hrun := t.run_matches_compatible_ranking rule.strategy [] π hcompat
    exact (ht π).symm.trans hrun.1
  have hle : (compatibleRankings result.observations.reverse).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hpos : 0 < (compatibleRankings result.observations.reverse).card :=
    Finset.card_pos.mpr hnonempty
  change (compatibleRankings result.observations.reverse).card = 1
  omega

theorem countingPotential_terminal_lower (rule : PotentialRule n)
    (t : DecisionTree n)
    (ht : t.Correct) (π : Ranking n)
    (hπ : Compatible π
      (t.run rule.strategy []).observations) :
    terminalPotentialLower n ≤
      countingPotential n
        (t.run rule.strategy []).observations.reverse := by
  rw [countingPotential, compatibleRankings_run_card_eq_one rule t ht]
  simp [terminalPotentialLower]

/-- An unconditional certified rule family. -/
noncomputable def countingCertifiedRuleFamily : CertifiedRuleFamily where
  rule := countingPotentialRule
  maxIncrease_eq := fun _ => rfl
  initial_upper := countingPotential_initial_upper
  terminal_lower := by
    intro n t ht π hπ
    exact countingPotential_terminal_lower (countingPotentialRule n) t ht π hπ

/-- The majority strategy proves the sharp information-theoretic leading
coefficient one in the semantic model. -/
theorem counting_adversary_one : HasAdversaryLeadingConstant 1 := by
  refine ⟨fun n => (countingUnitPotentialRule n).strategy,
    (3 / 2 : ℝ), by norm_num, ?_⟩
  intro n hn t ht
  constructor
  · exact (countingUnitPotentialRule n).run_consistent t
  · have hglobal := (countingUnitPotentialRule n).comparisons_lower_bound t
      (terminalPotentialLower n)
      (fun π hπ => countingPotential_terminal_lower
        (countingUnitPotentialRule n) t ht π hπ)
    have hinitial := countingPotential_initial_upper n
    have hbound : terminalPotentialLower n - (3 / 2 : ℝ) * n ≤
        (t.run (countingUnitPotentialRule n).strategy []).comparisons := by
      calc
        terminalPotentialLower n - (3 / 2 : ℝ) * n ≤
            terminalPotentialLower n - countingPotential n [] :=
          sub_le_sub_left hinitial _
        _ ≤ (t.run (countingUnitPotentialRule n).strategy []).comparisons * 1 := hglobal
        _ = (t.run (countingUnitPotentialRule n).strategy []).comparisons := by ring
    simpa [terminalPotentialLower] using hbound

theorem nLog2n_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ nLog2n n := by
  unfold nLog2n
  exact mul_nonneg (Nat.cast_nonneg n)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast hn))
      (Real.log_pos (by norm_num)).le)

/-- Any smaller leading coefficient follows from the majority adversary. -/
theorem hasAdversaryLeadingConstant_of_le_one {c : ℝ} (hc : c ≤ 1) :
    HasAdversaryLeadingConstant c := by
  rcases counting_adversary_one with ⟨strategy, C, hC, hforce⟩
  refine ⟨strategy, C, hC, ?_⟩
  intro n hn t ht
  rcases hforce n hn t ht with ⟨hcompat, hcost⟩
  refine ⟨hcompat, ?_⟩
  have hN := nLog2n_nonneg (n := n) (by omega)
  exact (by nlinarith : c * nLog2n n - C * n ≤
    1 * nLog2n n - C * n).trans hcost

end StrengthenedCurvature

/-- The repository's exact source-backed target, now unconditional. -/
theorem strengthened_curvature_adversary : StrengthenedCurvatureTarget :=
  StrengthenedCurvature.countingCertifiedRuleFamily.target

end SortingAdversary
