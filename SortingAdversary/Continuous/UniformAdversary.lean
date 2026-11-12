import SortingAdversary.Continuous.ControllerCorrect
import SortingAdversary.Continuous.ControllerAsymptotics
import SortingAdversary.Continuous.UniformStages

/-!
# The uniform continuous adversary

The bounded selector chooses the parameter once during initialization.
Its stage-zero value, 32, is an inactive sentinel: `Controller.start` then
uses the fixed label order. Every admitted parameter is at least 64, its
actual enumeration budget is at most the input size, and the selected
parameters tend to infinity.

`Program.execute` is the direct stateful implementation. Its equality to
the history-based strategy is proved, so transcript replay in the semantic
definition is not part of the work performed by an online query.
-/

namespace SortingAdversary.Continuous.UniformAdversary

open Filter
open scoped Topology

def parameter (n : ℕ) : ℕ := UniformStages.degree (UniformStages.selectedStage n)

structure Program (n : ℕ) where
  parameter : ℕ

def build (n : ℕ) : Program n := ⟨parameter n⟩

def Program.initial {n : ℕ} (p : Program n) : Controller.MachineState n :=
  Controller.start n p.parameter

def Program.step {n : ℕ} (p : Program n) :
    Controller.MachineState n → Query n → Answer × Controller.MachineState n :=
  Controller.step p.parameter

def Program.replay {n : ℕ} (p : Program n) (past : History n) : Controller.MachineState n :=
  past.reverse.foldl (fun s o => (p.step s o.query).2) p.initial

def Program.strategy {n : ℕ} (p : Program n) : Strategy n :=
  fun past q => (p.step (p.replay past) q).1

def strategy (n : ℕ) : Strategy n := (build n).strategy

@[simp] theorem strategy_eq (n : ℕ) : strategy n = Controller.strategy (parameter n) := rfl

@[simp] theorem Program.replay_cons {n : ℕ} (p : Program n) (o : Observation n) (past : History n) :
    p.replay (o :: past) = (p.step (p.replay past) o.query).2 := by
  simp [Program.replay, List.foldl_append]

def Program.execute {n : ℕ} (p : Program n) :
    DecisionTree n → Controller.MachineState n → RunResult n × Controller.MachineState n
  | .leaf output, s => (⟨output, [], 0⟩, s)
  | .compare q left right, s =>
    let r := p.step s q
    match r.1 with
    | .less =>
      let tail := p.execute left r.2
      (⟨tail.1.output, ⟨q, .less⟩ :: tail.1.observations, tail.1.comparisons + 1⟩, tail.2)
    | .greater =>
      let tail := p.execute right r.2
      (⟨tail.1.output, ⟨q, .greater⟩ :: tail.1.observations, tail.1.comparisons + 1⟩, tail.2)

theorem Program.execute_eq_run {n : ℕ} (p : Program n) (t : DecisionTree n) (past : History n) :
    (p.execute t (p.replay past)).1 = t.run p.strategy past := by
  induction t generalizing past with
  | leaf output => rfl
  | compare q left right ihL ihR =>
    cases h : (p.step (p.replay past) q).1 with
    | less =>
      have ht := ihL (⟨q, .less⟩ :: past)
      simpa only [Program.execute, DecisionTree.run, Program.strategy, h, Program.replay_cons] using
        congrArg (fun r : RunResult n =>
          (⟨r.output, ⟨q, .less⟩ :: r.observations, r.comparisons + 1⟩ : RunResult n)) ht
    | greater =>
      have ht := ihR (⟨q, .greater⟩ :: past)
      simpa only [Program.execute, DecisionTree.run, Program.strategy, h, Program.replay_cons] using
        congrArg (fun r : RunResult n =>
          (⟨r.output, ⟨q, .greater⟩ :: r.observations, r.comparisons + 1⟩ : RunResult n)) ht

theorem parameter_tendsto : Tendsto parameter atTop atTop :=
  UniformStages.selected_parameter_tendsto

theorem active_stage {n : ℕ} (hk : 64 ≤ parameter n) :
    0 < UniformStages.selectedStage n := by
  by_contra h
  have hz : UniformStages.selectedStage n = 0 := Nat.eq_zero_of_not_pos h
  norm_num [parameter, hz, UniformStages.degree] at hk

theorem enumeration_budget {n : ℕ} (hk : 64 ≤ parameter n) :
    UniformStages.enumerationBudget (parameter n) (by omega) ≤ n :=
  UniformStages.selected_enumerationBudget n (active_stage hk)

theorem consistent : SortingAdversary.Optimal.ConsistentFamily strategy := by
  intro n t
  rw [strategy_eq]
  exact Controller.consistent_parameter_schedule parameter
    (fun n hk => Controller.compareGuarantee n (parameter n) hk) n t

/-- The continuous paper's main online comparison theorem, for this
single concrete family and with every local guarantee discharged. -/
theorem asymptoticallyOptimal : SortingAdversary.Optimal.AsymptoticallyOptimal strategy := by
  change SortingAdversary.Optimal.AsymptoticallyOptimal (fun n => Controller.strategy (parameter n))
  exact Controller.asymptoticallyOptimal_of_eventual_compare_guarantee parameter parameter_tendsto
    (fun n hk => Controller.compareGuarantee n (parameter n) hk)

theorem worst_case :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : DecisionTree n, t.Correct →
        ∃ π : Ranking n, (1 - δ) * nLog2n n ≤ (t.cost π : ℝ) :=
  SortingAdversary.Optimal.asymptotic_worst_case strategy asymptoticallyOptimal

theorem prefix_count {n : ℕ} (hk : 64 ≤ parameter n) (h : History n)
    (hf : Follows (strategy n) h) :
    log2 (n.factorial : ℝ) - (1 + prefixOverhead (parameter n)) * h.length ≤
      log2 (transcriptCount h : ℝ) :=
  Controller.prefix_count (parameter n) hk h hf

noncomputable def error (n : ℕ) : ℝ := Controller.stageError parameter n

theorem error_nonneg (n : ℕ) : 0 ≤ error n := Controller.stageError_nonneg parameter n

theorem error_tendsto : Tendsto error atTop (𝓝 0) :=
  Controller.stageError_tendsto parameter parameter_tendsto

/-- The same initialized program and the same vanishing error sequence
work for every target partial order. -/
theorem production {n : ℕ} (h : History n) (hf : Follows (strategy n) h)
    (R : Item n → Item n → Prop) (assignment : Ranking n)
    (hcorrect : ∀ π, Compatible π h → Produces R assignment π) :
    (1 - error n) * (log2 (n.factorial : ℝ) - log2 (extensionCount R : ℝ)) ≤ h.length :=
  Controller.production_parameter_schedule parameter
    (fun n hk => Controller.compareGuarantee n (parameter n) hk) n h hf R assignment hcorrect

end SortingAdversary.Continuous.UniformAdversary
