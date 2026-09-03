import SortingAdversary.Strategy
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# A real-valued potential adversary

This file supplies the global bookkeeping used by the strengthened-curvature
argument.  Unlike `PotentialCertificate`, whose rational traces are convenient
for small finite certificates, the volumetric potential is genuinely
real-valued because it contains a logarithmic determinant.

The history seen by a `Strategy` is reverse chronological.  The theorem below
therefore telescopes the potential on that internal history, while separately
proving that the chronological transcript returned by `DecisionTree.run` is
compatible with a concrete ranking.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- A reverse-chronological history is feasible when some genuine ranking
satisfies all its observations. -/
def Feasible (h : History n) : Prop :=
  ∃ π : Ranking n, Compatible π h

@[simp] theorem feasible_nil (n : ℕ) : Feasible ([] : History n) := by
  exact ⟨Equiv.refl (Fin n), compatible_nil _⟩

/-- Add one answer to the reverse-chronological internal history. -/
def answerHistory (h : History n) (q : Query n) (a : Answer) : History n :=
  ⟨q, a⟩ :: h

/-- The local data needed to define a potential-minimizing adversary.

The step condition is deliberately existential.  A concrete geometric
development proves it by exhibiting one of the two trial points from the
one-comparison determinant theorem.
-/
structure PotentialRule (n : ℕ) where
  potential : History n → ℝ
  maxIncrease : ℝ
  maxIncrease_nonneg : 0 ≤ maxIncrease
  step : ∀ (h : History n) (q : Query n), Feasible h →
    ∃ a : Answer,
      Feasible (answerHistory h q a) ∧
        potential (answerHistory h q a) - potential h ≤ maxIncrease

namespace PotentialRule

/-- Choose the certified answer on feasible histories.  Its value on an
unreachable infeasible history is fixed only to make the strategy total. -/
noncomputable def answer (rule : PotentialRule n) (h : History n)
    (q : Query n) : Answer := by
  classical
  exact if hh : Feasible h then Classical.choose (rule.step h q hh) else .less

/-- The total history-dependent strategy induced by a potential rule. -/
noncomputable def strategy (rule : PotentialRule n) : Strategy n :=
  rule.answer

private theorem answer_spec (rule : PotentialRule n) (h : History n)
    (q : Query n) (hh : Feasible h) :
    Feasible (answerHistory h q (rule.answer h q)) ∧
      rule.potential (answerHistory h q (rule.answer h q)) - rule.potential h ≤
        rule.maxIncrease := by
  rw [answer, dif_pos hh]
  exact Classical.choose_spec (rule.step h q hh)

private theorem compatible_reverse_iff (π : Ranking n) (h : History n) :
    Compatible π h.reverse ↔ Compatible π h := by
  simp [Compatible, List.forall_iff_forall_mem]

/-- Along every generated path, the final internal history is feasible and
the potential increase is at most the path length times the local budget. -/
theorem run_invariant (rule : PotentialRule n) (t : DecisionTree n)
    (past : History n) (hpast : Feasible past) :
    Feasible ((t.run rule.strategy past).observations.reverse ++ past) ∧
      rule.potential ((t.run rule.strategy past).observations.reverse ++ past) -
          rule.potential past ≤
        (t.run rule.strategy past).comparisons * rule.maxIncrease := by
  induction t generalizing past with
  | leaf output =>
      simpa [DecisionTree.run] using And.intro hpast (le_refl (0 : ℝ))
  | compare q onLess onGreater ihLess ihGreater =>
      have hlocal := rule.answer_spec past q hpast
      cases hanswer : rule.answer past q with
      | less =>
          let o : Observation n := ⟨q, .less⟩
          have hlocal' : Feasible (o :: past) ∧
              rule.potential (o :: past) - rule.potential past ≤ rule.maxIncrease := by
            simpa [o, answerHistory, hanswer] using hlocal
          have hsub := ihLess (past := o :: past) hlocal'.1
          constructor
          · simpa [DecisionTree.run, strategy, hanswer, o, List.reverse_cons,
              List.append_assoc] using hsub.1
          · have hsum :
                rule.potential
                      ((onLess.run rule.strategy (o :: past)).observations.reverse ++
                        (o :: past)) -
                    rule.potential past ≤
                  ((onLess.run rule.strategy (o :: past)).comparisons + 1) *
                    rule.maxIncrease := by
              calc
                rule.potential
                      ((onLess.run rule.strategy (o :: past)).observations.reverse ++
                        (o :: past)) -
                    rule.potential past =
                    (rule.potential
                          ((onLess.run rule.strategy (o :: past)).observations.reverse ++
                            (o :: past)) -
                        rule.potential (o :: past)) +
                      (rule.potential (o :: past) - rule.potential past) := by ring
                _ ≤ (onLess.run rule.strategy (o :: past)).comparisons *
                        rule.maxIncrease + rule.maxIncrease :=
                  add_le_add hsub.2 hlocal'.2
                _ = ((onLess.run rule.strategy (o :: past)).comparisons + 1) *
                        rule.maxIncrease := by ring
            simpa [DecisionTree.run, strategy, hanswer, o, List.reverse_cons,
              List.append_assoc] using hsum
      | greater =>
          let o : Observation n := ⟨q, .greater⟩
          have hlocal' : Feasible (o :: past) ∧
              rule.potential (o :: past) - rule.potential past ≤ rule.maxIncrease := by
            simpa [o, answerHistory, hanswer] using hlocal
          have hsub := ihGreater (past := o :: past) hlocal'.1
          constructor
          · simpa [DecisionTree.run, strategy, hanswer, o, List.reverse_cons,
              List.append_assoc] using hsub.1
          · have hsum :
                rule.potential
                      ((onGreater.run rule.strategy (o :: past)).observations.reverse ++
                        (o :: past)) -
                    rule.potential past ≤
                  ((onGreater.run rule.strategy (o :: past)).comparisons + 1) *
                    rule.maxIncrease := by
              calc
                rule.potential
                      ((onGreater.run rule.strategy (o :: past)).observations.reverse ++
                        (o :: past)) -
                    rule.potential past =
                    (rule.potential
                          ((onGreater.run rule.strategy (o :: past)).observations.reverse ++
                            (o :: past)) -
                        rule.potential (o :: past)) +
                      (rule.potential (o :: past) - rule.potential past) := by ring
                _ ≤ (onGreater.run rule.strategy (o :: past)).comparisons *
                        rule.maxIncrease + rule.maxIncrease :=
                  add_le_add hsub.2 hlocal'.2
                _ = ((onGreater.run rule.strategy (o :: past)).comparisons + 1) *
                        rule.maxIncrease := by ring
            simpa [DecisionTree.run, strategy, hanswer, o, List.reverse_cons,
              List.append_assoc] using hsum

/-- A generated transcript is compatible with a genuine ranking. -/
theorem run_consistent (rule : PotentialRule n) (t : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (t.run rule.strategy []).observations := by
  obtain ⟨π, hπ⟩ := (rule.run_invariant t [] (feasible_nil n)).1
  refine ⟨π, ?_⟩
  apply (compatible_reverse_iff π (t.run rule.strategy []).observations).1
  simpa using hπ

/-- Global real-potential lower bound for a correct sorting tree. -/
theorem comparisons_lower_bound (rule : PotentialRule n) (t : DecisionTree n)
    (terminal : ℝ) (hterminal :
      ∀ π : Ranking n,
        Compatible π (t.run rule.strategy []).observations →
        terminal ≤
          rule.potential (t.run rule.strategy []).observations.reverse) :
    terminal - rule.potential [] ≤
      (t.run rule.strategy []).comparisons * rule.maxIncrease := by
  obtain ⟨π, hπ⟩ := rule.run_consistent t
  calc
    terminal - rule.potential [] ≤
        rule.potential (t.run rule.strategy []).observations.reverse -
          rule.potential [] := sub_le_sub_right (hterminal π hπ) _
    _ ≤ (t.run rule.strategy []).comparisons * rule.maxIncrease := by
      simpa using (rule.run_invariant t [] (feasible_nil n)).2

end PotentialRule
end StrengthenedCurvature
end SortingAdversary
