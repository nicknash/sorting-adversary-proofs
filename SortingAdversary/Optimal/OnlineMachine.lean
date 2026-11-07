import SortingAdversary.Optimal.PublicLegality

/-!
# Stateful implementations of transcript strategies

A finite-state transition is run directly against a comparison tree. Replaying
the previous queries gives an extensionally identical `Strategy`, so the
repository's sorting semantics apply to the stateful implementation. A public
order preserved by every transition proves legality of every finite run.
-/

namespace SortingAdversary.Optimal.OnlineMachine

open SparseClosure PublicOrder PublicLegality

structure Machine (n : ℕ) where
  State : Type
  initial : State
  step : State → Query n → Answer × State
  rows : State → Rows (Fin n)
  ordered : ∀ s, IsOrder (rows s)
  monotone : ∀ s q x y, rows s x y = true → rows (step s q).2 x y = true
  answered : ∀ s q, rows (step s q).2
    (earlier ⟨q, (step s q).1⟩) (later ⟨q, (step s q).1⟩) = true

namespace Machine

variable {n : ℕ}

/-- Transcript replay is the semantic presentation of a deterministic
stateful implementation; previous supplied answers are not trusted as state. -/
def replay (m : Machine n) (past : History n) : m.State :=
  past.reverse.foldl (fun s o => (m.step s o.query).2) m.initial

def strategy (m : Machine n) : Strategy n := fun past q => (m.step (m.replay past) q).1

@[simp] theorem replay_nil (m : Machine n) : m.replay [] = m.initial := rfl

@[simp] theorem replay_cons (m : Machine n) (o : Observation n) (past : History n) :
    m.replay (o :: past) = (m.step (m.replay past) o.query).2 := by
  simp [replay, List.foldl_append]

def execute (m : Machine n) : DecisionTree n → m.State → RunResult n × m.State
  | .leaf output, s => (⟨output, [], 0⟩, s)
  | .compare q left right, s =>
      let result := m.step s q
      match result.1 with
      | .less =>
          let tail := m.execute left result.2
          (⟨tail.1.output, ⟨q, .less⟩ :: tail.1.observations, tail.1.comparisons + 1⟩, tail.2)
      | .greater =>
          let tail := m.execute right result.2
          (⟨tail.1.output, ⟨q, .greater⟩ :: tail.1.observations, tail.1.comparisons + 1⟩, tail.2)

/-- Direct stateful execution has exactly the transcript, output, and number
of physical comparisons of the canonical history-dependent strategy. -/
theorem execute_eq_run (m : Machine n) (t : DecisionTree n) (past : History n) :
    (m.execute t (m.replay past)).1 = t.run m.strategy past := by
  induction t generalizing past with
  | leaf output => rfl
  | compare q left right ihL ihR =>
    cases h : (m.step (m.replay past) q).1 with
    | less =>
      have ht := ihL (⟨q, .less⟩ :: past)
      simpa only [execute, DecisionTree.run, strategy, h, replay_cons] using
        congrArg (fun r : RunResult n =>
          (⟨r.output, ⟨q, .less⟩ :: r.observations, r.comparisons + 1⟩ : RunResult n)) ht
    | greater =>
      have ht := ihR (⟨q, .greater⟩ :: past)
      simpa only [execute, DecisionTree.run, strategy, h, replay_cons] using
        congrArg (fun r : RunResult n =>
          (⟨r.output, ⟨q, .greater⟩ :: r.observations, r.comparisons + 1⟩ : RunResult n)) ht

/-- Every ranking extending the final public order also extends the initial
one and agrees strictly with every answer along the execution. -/
theorem execute_respects (m : Machine n) (t : DecisionTree n) (s : m.State)
    (π : Ranking n) (hπ : Respects (m.rows (m.execute t s).2) π) :
    Respects (m.rows s) π ∧ Compatible π (m.execute t s).1.observations := by
  induction t generalizing s with
  | leaf output => exact ⟨hπ, compatible_nil π⟩
  | compare q left right ihL ihR =>
    cases h : (m.step s q).1 with
    | less =>
      have ht : Respects (m.rows (m.execute left (m.step s q).2).2) π := by
        simpa only [execute, h] using hπ
      obtain ⟨hnext, htail⟩ := ihL (m.step s q).2 ht
      refine ⟨fun x y hxy => hnext x y (m.monotone s q x y hxy), ?_⟩
      have hrow := m.answered s q
      rw [h] at hrow
      have hholds : (Observation.mk q .less).Holds π :=
        (holds_iff _ _).mpr (strict_of_row hnext hrow (earlier_ne_later _))
      simpa only [execute, h] using (compatible_cons π ⟨q, .less⟩ _).mpr ⟨hholds, htail⟩
    | greater =>
      have ht : Respects (m.rows (m.execute right (m.step s q).2).2) π := by
        simpa only [execute, h] using hπ
      obtain ⟨hnext, htail⟩ := ihR (m.step s q).2 ht
      refine ⟨fun x y hxy => hnext x y (m.monotone s q x y hxy), ?_⟩
      have hrow := m.answered s q
      rw [h] at hrow
      have hholds : (Observation.mk q .greater).Holds π :=
        (holds_iff _ _).mpr (strict_of_row hnext hrow (earlier_ne_later _))
      simpa only [execute, h] using (compatible_cons π ⟨q, .greater⟩ _).mpr ⟨hholds, htail⟩

theorem execute_consistent (m : Machine n) (t : DecisionTree n) (s : m.State) :
    ∃ π : Ranking n, Compatible π (m.execute t s).1.observations := by
  let π := rankingExtension (m.rows (m.execute t s).2)
  exact ⟨π, (m.execute_respects t s π (rankingExtension_respects (m.ordered _))).2⟩

theorem strategy_consistent (m : Machine n) (t : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (t.run m.strategy []).observations := by
  rw [← m.execute_eq_run t [], m.replay_nil]
  exact m.execute_consistent t m.initial

end Machine
end SortingAdversary.Optimal.OnlineMachine
