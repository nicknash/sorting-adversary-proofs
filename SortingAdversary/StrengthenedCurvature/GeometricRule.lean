import SortingAdversary.StrengthenedCurvature.InformativeHistory

/-!
# Completing the response rule from informative transitions

The determinant argument is needed only when neither orientation of a query is
already implied.  This file proves, once and for all, that a local theorem for
those informative queries extends to a total strategy for arbitrary sorting
algorithms, including repeated and transitively implied comparisons.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- Potential data for the retained history DAG. -/
structure InformativePotentialRule (n : ℕ) where
  potential : History n → ℝ
  maxIncrease : ℝ
  maxIncrease_nonneg : 0 ≤ maxIncrease
  informativeStep : ∀ (h : History n) (q : Query n), Feasible h →
    ¬(Knowledge.ofHistory h).rel q.left q.right →
    ¬(Knowledge.ofHistory h).rel q.right q.left →
    ∃ a : Answer,
      Feasible (answerHistory h q a) ∧
        potential (answerHistory h q a) - potential h ≤ maxIncrease

namespace InformativePotentialRule

/-- The potential on a raw algorithm transcript is the geometric potential of
its informative retained subhistory. -/
noncomputable def rawPotential (rule : InformativePotentialRule n)
    (h : History n) : ℝ :=
  rule.potential (retainedHistory h)

/-- Extend an informative-query rule to every possible query.  Entailed
comparisons choose their forced answer and have zero potential increase. -/
noncomputable def toPotentialRule (rule : InformativePotentialRule n) :
    PotentialRule n where
  potential := rule.rawPotential
  maxIncrease := rule.maxIncrease
  maxIncrease_nonneg := rule.maxIncrease_nonneg
  step := by
    intro past q hpast
    let retained := retainedHistory past
    by_cases hless : (Knowledge.ofHistory retained).rel q.left q.right
    · refine ⟨.less, ?_, ?_⟩
      · obtain ⟨π, hπ⟩ := hpast
        have hπretained : Compatible π retained :=
          compatible_retainedHistory π past hπ
        have ho : (Observation.mk q .less).Holds π := by
          rw [holds_iff_lower_lt_upper]
          exact Knowledge.realizes_ofHistory π retained hπretained hless
        exact ⟨π, (compatible_cons π ⟨q, .less⟩ past).2 ⟨ho, hπ⟩⟩
      · have hentails : EntailedBy (Observation.mk q .less) retained := by
          simpa [EntailedBy, lower, upper] using hless
        simp [rawPotential,
          retainedHistory_answerHistory_of_entailed past q .less hentails,
          rule.maxIncrease_nonneg]
    · by_cases hgreater : (Knowledge.ofHistory retained).rel q.right q.left
      · refine ⟨.greater, ?_, ?_⟩
        · obtain ⟨π, hπ⟩ := hpast
          have hπretained : Compatible π retained :=
            compatible_retainedHistory π past hπ
          have ho : (Observation.mk q .greater).Holds π := by
            rw [holds_iff_lower_lt_upper]
            exact Knowledge.realizes_ofHistory π retained hπretained hgreater
          exact ⟨π, (compatible_cons π ⟨q, .greater⟩ past).2 ⟨ho, hπ⟩⟩
        · have hentails : EntailedBy (Observation.mk q .greater) retained := by
            simpa [EntailedBy, lower, upper] using hgreater
          simp [rawPotential,
            retainedHistory_answerHistory_of_entailed past q .greater hentails,
            rule.maxIncrease_nonneg]
      · obtain ⟨a, hfeasible, hincrease⟩ :=
          rule.informativeStep retained q (feasible_retainedHistory hpast) hless hgreater
        refine ⟨a, ?_, ?_⟩
        · obtain ⟨π, hπ⟩ := hfeasible
          have hparts := (compatible_cons π ⟨q, a⟩ retained).1 hπ
          exact ⟨π, (compatible_cons π ⟨q, a⟩ past).2
            ⟨hparts.1, (compatible_retainedHistory_iff π past).1 hparts.2⟩⟩
        · have hnot : ¬EntailedBy (Observation.mk q a) retained := by
            cases a with
            | less =>
                simpa [EntailedBy, lower, upper] using hless
            | greater =>
                simpa [EntailedBy, lower, upper] using hgreater
          change rule.potential (retainedHistory (answerHistory past q a)) -
              rule.potential (retainedHistory past) ≤ rule.maxIncrease
          rw [retainedHistory_answerHistory_of_not_entailed past q a hnot]
          simpa [answerHistory] using hincrease

end InformativePotentialRule
end StrengthenedCurvature
end SortingAdversary
