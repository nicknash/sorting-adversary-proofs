import SortingAdversary.Continuous.UniformInitializationWork
import SortingAdversary.Continuous.MachineWork
import SortingAdversary.Continuous.ControllerWorkBounds
import SortingAdversary.Continuous.ConcreteRoutines

/-!
# A concrete measured uniform online program

Initialization executes the counted parameter selector and constructs stored
data. Each subsequent query takes only the current stored state. The replay
function below is a semantic specification used to prove agreement with the
history-based adversary; the online transition does not replay the transcript.

All component budgets in the final per-query theorem are instantiated by the
actual admitted parameter. Its only state premise is reachability under this
program, and that premise is preserved by every actual transition.
-/

namespace SortingAdversary.Continuous.UniformMachineWork

open SortingAdversary.Optimal
open ControllerWork

abbrev Program (n : ℕ) := UniformInitializationWork.Setup n
abbrev State (n : ℕ) := UniformInitializationWork.InitialState n
abbrev build (n : ℕ) : PrimitiveWork.Result (Program n) := UniformInitializationWork.build n

variable {n : ℕ}

def Program.routines (p : Program n) : Routines n p.parameter :=
  ConcreteRoutines.routines n p.parameter p.positive

def toMachine (p : Program n) : State n → MachineWork.State p.routines
  | .inl memory => .active memory
  | .inr ranks => .frozen ranks

def fromMachine (p : Program n) : MachineWork.State p.routines → State n
  | .active memory => .inl memory
  | .frozen ranks => .inr ranks

abbrev view (s : State n) : Controller.MachineState n := UniformInitializationWork.initialView s

@[simp] theorem toMachine_view (p : Program n) (s : State n) :
    MachineWork.view p.routines (toMachine p s) = view s := by cases s <;> rfl

@[simp] theorem fromMachine_view (p : Program n) (s : MachineWork.State p.routines) :
    view (fromMachine p s) = MachineWork.view p.routines s := by cases s <;> rfl

def answerView (a : Answer × State n) : Answer × Controller.MachineState n := (a.1, view a.2)

/-- The parameter and cutoff are stored once. Six additional operations
cover stored scalar reads, constructor conversion and result construction. -/
def Program.step (p : Program n) (s : State n) (q : Query n) :
    PrimitiveWork.Result (Answer × State n) :=
  let result := MachineWork.step p.routines p.cutoff (toMachine p s) q
  ⟨(result.value.1, fromMachine p result.value.2), result.work + 6⟩

@[simp] theorem Program.frozen_work (p : Program n) (ranks : Vector (Fin n) n) (q : Query n) :
    (p.step (.inr ranks) q).work = 10 := rfl

@[simp] theorem Program.frozen_state (p : Program n) (ranks : Vector (Fin n) n) (q : Query n) :
    (p.step (.inr ranks) q).value.2 = .inr ranks := rfl

theorem Program.step_value (p : Program n) (hcut : p.cutoff = Controller.horizon n)
    (s : State n) (q : Query n) :
    answerView (p.step s q).value = Controller.step p.parameter (view s) q := by
  have hv := MachineWork.step_value p.routines (toMachine p s) q
  simpa only [Program.step, hcut, answerView, MachineWork.answerView,
    fromMachine_view, toMachine_view] using hv

def Program.replay (p : Program n) (past : History n) : State n :=
  past.reverse.foldl (fun s o => (p.step s o.query).value.2) p.initial

@[simp] theorem Program.replay_cons (p : Program n) (o : Observation n) (past : History n) :
    p.replay (o :: past) = (p.step (p.replay past) o.query).value.2 := by
  simp [Program.replay, List.foldl_append]

theorem Program.replay_value (p : Program n) (hcut : p.cutoff = Controller.horizon n)
    (hi : view p.initial = Controller.start n p.parameter) (past : History n) :
    view (p.replay past) = Controller.replay p.parameter past := by
  induction past with
  | nil => exact hi
  | cons o past ih =>
    rw [Program.replay_cons, Controller.replay_cons]
    have hv := congrArg Prod.snd (p.step_value hcut (p.replay past) o.query)
    simpa only [answerView, ih] using hv

def Program.strategy (p : Program n) : Strategy n := fun past q => (p.step (p.replay past) q).value.1

theorem Program.strategy_value (p : Program n) (hcut : p.cutoff = Controller.horizon n)
    (hi : view p.initial = Controller.start n p.parameter) :
    p.strategy = Controller.strategy p.parameter := by
  funext past q
  have hv := congrArg Prod.fst (p.step_value hcut (p.replay past) q)
  simpa only [answerView, Program.strategy, Controller.strategy, p.replay_value hcut hi] using hv

/-- Equality holds on arbitrary supplied histories, not just those following
the strategy's answers. -/
theorem strategy_eq (n : ℕ) : (build n).value.strategy = UniformAdversary.strategy n := by
  calc
    _ = Controller.strategy (build n).value.parameter :=
      (build n).value.strategy_value (UniformInitializationWork.build_cutoff n)
        (UniformInitializationWork.build_initial n)
    _ = _ := by rw [UniformInitializationWork.build_parameter, UniformAdversary.strategy_eq]

theorem replay_value (n : ℕ) (past : History n) :
    view ((build n).value.replay past) = Controller.replay (UniformAdversary.parameter n) past := by
  simpa only [UniformInitializationWork.build_parameter] using
    (build n).value.replay_value (UniformInitializationWork.build_cutoff n)
      (UniformInitializationWork.build_initial n) past

def Program.Reachable (p : Program n) (s : State n) : Prop := ∃ past, p.replay past = s

theorem Program.initial_reachable (p : Program n) : p.Reachable p.initial := ⟨[], rfl⟩

theorem Program.step_reachable (p : Program n) {s : State n} (hs : p.Reachable s) (q : Query n) :
    p.Reachable (p.step s q).value.2 := by
  obtain ⟨past, rfl⟩ := hs
  exact ⟨⟨q, (p.step (p.replay past) q).value.1⟩ :: past, p.replay_cons _ _⟩

def queryBound (n : ℕ) : ℕ :=
  (n + 7) * (2 * ConcreteRoutines.wordBound n + 3) + 100 * (n + 1) ^ 4 + n ^ 2 + 20

private theorem admitted_calls {n k : ℕ} (hk : 0 < k)
    (hparameter : k = UniformAdversary.parameter n) (hactive : 64 ≤ k) :
    CallBounds (ConcreteRoutines.routines n k hk) (depthCap n) (gridCap n) (historyCap n)
        (ConcreteRoutines.wordBound n) ∧ UniformStages.enumerationBudget k hk ≤ n := by
  subst k
  have hstage := UniformAdversary.active_stage hactive
  have hcap : UniformStages.Recipe.budget.need (UniformStages.selectedStage n) ≤ n :=
    (CappedStageScan.stage_need UniformStages.Recipe.budget n hstage).trans
      (Parameters.logCap_le_input n)
  exact ⟨ConcreteRoutines.callBounds_admitted n (UniformStages.selectedStage n) hcap,
    UniformAdversary.enumeration_budget hactive⟩

/-- This bound has no local-routine or component-work hypotheses. -/
theorem per_query (n : ℕ) (s : State n) (hs : (build n).value.Reachable s) (q : Query n) :
    ((build n).value.step s q).work ≤ queryBound n := by
  obtain ⟨past, rfl⟩ := hs
  let p : Program n := (build n).value
  have hparameter : p.parameter = UniformAdversary.parameter n :=
    UniformInitializationWork.build_parameter n
  have hcut : p.cutoff = Controller.horizon n := UniformInitializationWork.build_cutoff n
  have hv := p.replay_value hcut (UniformInitializationWork.build_initial n) past
  have hb : MachineWork.QueryBudget p.routines (ConcreteRoutines.wordBound n)
      (toMachine p (p.replay past)) q := by
    cases hm : p.replay past with
    | inr ranks => trivial
    | inl memory =>
      have hr : Controller.replay p.parameter past = .active memory.memory := by
        simpa only [hm, view, UniformInitializationWork.initialView] using hv.symm
      have hrun := Controller.replay_runtimeInvariant p.parameter p.positive past
      rw [hr] at hrun
      refine ⟨hrun.2.2.2.trans (Controller.horizon_le_square n), fun _ => ?_⟩
      have hc := admitted_calls p.positive hparameter hrun.1
      exact reachable_compare_budget p.routines hrun.1 hc.1 past memory hr hc.2 q
  have hw := MachineWork.step_work p.routines (ConcreteRoutines.wordBound n)
    (toMachine p (p.replay past)) q hb
  change (p.step (p.replay past) q).work ≤ queryBound n
  simp only [Program.step, hcut]
  unfold queryBound
  omega

theorem queryBound_polynomial (n : ℕ) : queryBound n ≤ 100000000000 * (n + 3) ^ 17 := by
  have hp : 1 ≤ (n + 3) ^ 16 := Nat.one_le_pow _ _ (by omega)
  have hf : 2 * ConcreteRoutines.wordBound n + 3 ≤ 2000000003 * (n + 3) ^ 16 := by
    unfold ConcreteRoutines.wordBound
    omega
  have hm := Nat.mul_le_mul (show n + 7 ≤ 3 * (n + 3) by omega) hf
  have hm' : (n + 7) * (2 * ConcreteRoutines.wordBound n + 3) ≤
      6000000009 * (n + 3) ^ 17 := by
    convert hm using 1; ring
  have hfour : (n + 1) ^ 4 ≤ (n + 3) ^ 17 :=
    (Nat.pow_le_pow_left (by omega) 4).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have htwo : n ^ 2 ≤ (n + 3) ^ 17 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hpos : 1 ≤ (n + 3) ^ 17 := Nat.one_le_pow _ _ (by omega)
  unfold queryBound
  omega

/-- One fixed polynomial bounds every subsequent query, including arbitrarily
many queries after the machine freezes. -/
theorem per_query_polynomial (n : ℕ) (s : State n) (hs : (build n).value.Reachable s) (q : Query n) :
    ((build n).value.step s q).work ≤ 100000000000 * (n + 3) ^ 17 :=
  (per_query n s hs q).trans (queryBound_polynomial n)

theorem initialization_work (n : ℕ) :
    (build n).work ≤ (7 * UniformStages.Recipe.budget.nodes + 100) * (n + 1) ^ 2 :=
  UniformInitializationWork.build_work n

/-- The measured program realizes the same adversary as the proved uniform
continuous comparison theorem. -/
theorem asymptoticallyOptimal :
    SortingAdversary.Optimal.AsymptoticallyOptimal (fun n => (build n).value.strategy) := by
  simpa only [strategy_eq] using UniformAdversary.asymptoticallyOptimal

end SortingAdversary.Continuous.UniformMachineWork
