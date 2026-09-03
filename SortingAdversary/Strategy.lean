import SortingAdversary.DecisionTree

/-!
# Adaptive adversaries and their executions

A strategy sees the previous transcript and the next query.  `run` records the
answers supplied along the chosen root-to-leaf path.  The main semantic lemma
proves that any concrete ranking compatible with that transcript follows the
same path through the ordinary decision-tree semantics.
-/

namespace SortingAdversary

/-- A deterministic, history-dependent comparison adversary. -/
abbrev Strategy (n : ℕ) := History n → Query n → Answer

/-- The observable result of running a decision tree against a strategy. -/
structure RunResult (n : ℕ) where
  output : Ranking n
  observations : History n
  comparisons : ℕ

namespace DecisionTree

/-- Execute a decision tree against an adaptive strategy.

The `past` argument is supplied to the strategy in reverse chronological order.
The returned `observations` are in chronological order along the new path.
-/
def run : DecisionTree n → Strategy n → History n → RunResult n
  | .leaf output, _, _ =>
      { output := output, observations := [], comparisons := 0 }
  | .compare q onLess onGreater, strategy, past =>
      match strategy past q with
      | .less =>
          let o : Observation n := ⟨q, .less⟩
          let sub := onLess.run strategy (o :: past)
          { output := sub.output
            observations := o :: sub.observations
            comparisons := sub.comparisons + 1 }
      | .greater =>
          let o : Observation n := ⟨q, .greater⟩
          let sub := onGreater.run strategy (o :: past)
          { output := sub.output
            observations := o :: sub.observations
            comparisons := sub.comparisons + 1 }

@[simp] theorem run_leaf (output : Ranking n) (strategy : Strategy n) (past : History n) :
    (DecisionTree.leaf output).run strategy past =
      { output := output, observations := [], comparisons := 0 } := by
  rfl

/-- The recorded transcript has exactly one observation per comparison. -/
theorem run_observations_length (t : DecisionTree n) (strategy : Strategy n)
    (past : History n) :
    (t.run strategy past).observations.length = (t.run strategy past).comparisons := by
  induction t generalizing past with
  | leaf output => simp [run]
  | compare q onLess onGreater ihLess ihGreater =>
      cases hanswer : strategy past q with
      | less =>
          simp [run, hanswer, ihLess]
      | greater =>
          simp [run, hanswer, ihGreater]

/-- A compatible ranking follows the same branch, reaches the same leaf, and
incurs the same cost as the adversarial execution. -/
theorem run_matches_compatible_ranking (t : DecisionTree n) (strategy : Strategy n)
    (past : History n) (π : Ranking n)
    (hcompat : Compatible π (t.run strategy past).observations) :
    t.evaluate π = (t.run strategy past).output ∧
      t.cost π = (t.run strategy past).comparisons := by
  induction t generalizing past with
  | leaf output =>
      simp [run, evaluate, cost]
  | compare q onLess onGreater ihLess ihGreater =>
      cases hanswer : strategy past q with
      | less =>
          let o : Observation n := ⟨q, .less⟩
          have hcompat' : Compatible π
              (o :: (onLess.run strategy (o :: past)).observations) := by
            simpa [run, hanswer, o] using hcompat
          have hparts :=
            (compatible_cons π o (onLess.run strategy (o :: past)).observations).1 hcompat'
          have hlt : π q.left < π q.right := by
            simpa [o, Observation.Holds] using hparts.1
          have houtcome : q.outcome π = .less := by
            simp [Query.outcome, hlt]
          have ih := ihLess (past := o :: past) hparts.2
          constructor
          · simpa [evaluate, run, hanswer, o, houtcome] using ih.1
          · simpa [cost, run, hanswer, o, houtcome] using ih.2
      | greater =>
          let o : Observation n := ⟨q, .greater⟩
          have hcompat' : Compatible π
              (o :: (onGreater.run strategy (o :: past)).observations) := by
            simpa [run, hanswer, o] using hcompat
          have hparts :=
            (compatible_cons π o (onGreater.run strategy (o :: past)).observations).1 hcompat'
          have hgt : π q.right < π q.left := by
            simpa [o, Observation.Holds] using hparts.1
          have hnlt : ¬ π q.left < π q.right :=
            not_lt_of_ge (le_of_lt hgt)
          have houtcome : q.outcome π = .greater := by
            simp [Query.outcome, hnlt]
          have ih := ihGreater (past := o :: past) hparts.2
          constructor
          · simpa [evaluate, run, hanswer, o, houtcome] using ih.1
          · simpa [cost, run, hanswer, o, houtcome] using ih.2

end DecisionTree

/-- A checkable certificate that one strategy forces at least `k` comparisons.

The two fields deliberately separate consistency from the potential/counting
argument.  An adversary-specific development must prove both.
-/
structure AdversaryCertificate (n k : ℕ) where
  strategy : Strategy n
  consistent : ∀ t : DecisionTree n,
    ∃ π : Ranking n, Compatible π (t.run strategy []).observations
  long : ∀ t : DecisionTree n, t.Correct →
    k ≤ (t.run strategy []).comparisons

/-- The generic adversary principle: a certified long, consistent interaction
produces an ordinary worst-case input for every correct sorting tree. -/
theorem lower_bound_of_adversary_certificate (cert : AdversaryCertificate n k)
    (t : DecisionTree n) (ht : t.Correct) : t.WorstCaseAtLeast k := by
  obtain ⟨π, hcompat⟩ := cert.consistent t
  refine ⟨π, ?_⟩
  have hrun := t.run_matches_compatible_ranking cert.strategy [] π hcompat
  rw [hrun.2]
  exact cert.long t ht

end SortingAdversary
