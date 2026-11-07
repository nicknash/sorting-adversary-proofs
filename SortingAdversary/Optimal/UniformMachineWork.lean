import SortingAdversary.Optimal.UniformRoutingWork
import SortingAdversary.Optimal.UniformSelectionWork
import SortingAdversary.Optimal.UniformInitialWork
import SortingAdversary.Optimal.UniformAdversary

/-!
# The complete counted uniform online adversary

`build` executes the bounded stage selection, builds both oracle
radii, and constructs the initial tree. Its result contains a stateful step
function: previous queries are never replayed by this implementation. The
full strategy of this program equals the already verified uniform adversary.

All counting, repair, routing, representation and initialization routines are
concrete. The uniform work bounds apply to every state admitted by the
machine's maintained invariants, including the permanent frozen state.
-/

namespace SortingAdversary.Optimal.UniformMachineWork

open PrimitiveWork UniformStage PublicLegality

variable {n j : ℕ}

def queryBound (n : ℕ) : ℕ := MeasuredController.stepBound n (UniformRoutingWork.bound n)

/-- A legal online machine, its measured transition, and exact agreement
with the optimal adversary. The equality and bounds erase at runtime. -/
structure Program (n : ℕ) where
  machine : OnlineMachine.Machine n
  step : machine.State → Query n → Result (Answer × machine.State)
  step_value : ∀ state query, (step state query).value = machine.step state query
  step_work : ∀ state query, (step state query).work ≤ queryBound n
  actual : machine.strategy = UniformAdversary.strategy n

/-- The clock is computed from a counted binary logarithm. -/
def clock (n : ℕ) : Result ℕ :=
  let logarithm := HubEnumerationWork.logTwo (n + 1)
  ⟨2 * n * (logarithm.value + 1), logarithm.work + 4⟩

@[simp] theorem clock_value (n : ℕ) : (clock n).value = UniformAdversary.cutoff n := by
  simp only [clock, HubEnumerationWork.logTwo_value, UniformAdversary.cutoff, Parameters.logCap]

theorem clock_work (n : ℕ) : (clock n).work ≤ 3 * n + 8 := by
  have h := HubEnumerationWork.logTwo_work_le (n + 1)
  change (HubEnumerationWork.logTwo (n + 1)).work + 4 ≤ _
  omega

def fixed (n : ℕ) (actual : (UniformAdversary.fixedMachine n).strategy = UniformAdversary.strategy n) :
    Program n where
  machine := UniformAdversary.fixedMachine n
  step _ query := ⟨(UniformAdversary.fixedAnswer query, ()), 3⟩
  step_value _ _ := rfl
  step_work _ _ := by
    change 3 ≤ queryBound n
    unfold queryBound MeasuredController.stepBound
    omega
  actual := actual

/-- Install the already constructed initial state without invoking the
reference machine's member enumeration during construction. -/
def acceptedMachine (N : ℕ) (a : Accepted (Parameters.logCap (N + 2)) j)
    (data : UniformPreparedWork.Data a) (cutoff : ℕ)
    (initial : MeasuredController.Active a.controller (N + 2)) : OnlineMachine.Machine (N + 2) where
  State := MeasuredController.State a.controller (N + 2) cutoff
  initial := .active ⟨0, Nat.succ_pos _⟩ initial
  step state query := (MeasuredController.step (UniformRoutingWork.executor a data) state query).value
  rows := MeasuredController.rows
  ordered := (MeasuredController.machine a.controller N cutoff (UniformRoutingWork.executor a data)).ordered
  monotone := (MeasuredController.machine a.controller N cutoff (UniformRoutingWork.executor a data)).monotone
  answered := (MeasuredController.machine a.controller N cutoff (UniformRoutingWork.executor a data)).answered

theorem acceptedMachine_eq (N : ℕ) (a : Accepted (Parameters.logCap (N + 2)) j)
    (data : UniformPreparedWork.Data a) (cutoff : ℕ)
    (initial : MeasuredController.Active a.controller (N + 2))
    (hi : initial = MeasuredController.Active.initial a.controller N) :
    acceptedMachine N a data cutoff initial =
      MeasuredController.machine a.controller N cutoff (UniformRoutingWork.executor a data) := by
  subst initial
  rfl

def admitted (N : ℕ) (a : Accepted (Parameters.logCap (N + 2)) j)
    (data : UniformPreparedWork.Data a) (cutoff : ℕ) (hclock : cutoff = UniformAdversary.cutoff (N + 2))
    (initial : MeasuredController.Active a.controller (N + 2))
    (hi : initial = MeasuredController.Active.initial a.controller N)
    (hstage : selectController (N + 2) = some a.controller) : Program (N + 2) where
  machine := acceptedMachine N a data cutoff initial
  step := MeasuredController.step (UniformRoutingWork.executor a data)
  step_value _ _ := rfl
  step_work state query := MeasuredController.step_work_le (UniformRoutingWork.executor a data)
    (UniformRoutingWork.bound (N + 2)) (UniformRoutingWork.executor_bound a data) state query
  actual := by
    rw [acceptedMachine_eq N a data cutoff initial hi]
    rw [MeasuredController.strategy_eq, hclock]
    exact (congrArg OnlineMachine.Machine.strategy (UniformAdversary.machine_of_admitted N a.controller hstage)).symm

def afterSelection (N : ℕ) (selected : UniformSelectionWork.Selected (N + 2)) : Result (Program (N + 2)) :=
  match hselected : selected.decision with
  | .fallback =>
    have hstage : selectController (N + 2) = none := by
      unfold selectController
      rw [← selected.actual, hselected]
    ⟨fixed (N + 2) (by
      change _ = (UniformAdversary.machine (N + 2)).strategy
      rw [UniformAdversary.machine_of_fallback N hstage]), 4⟩
  | .accepted j hj a =>
    have hstage : selectController (N + 2) = some a.controller := by
      unfold selectController
      rw [← selected.actual, hselected]
    let prepared := UniformPreparedWork.prepare a
    let initial := UniformInitialWork.active a.controller N
    let cutoff := clock (N + 2)
    ⟨admitted N a prepared.value cutoff.value (clock_value _) initial.value (UniformInitialWork.active_eq _ _) hstage,
      prepared.work + initial.work + cutoff.work + 20⟩

theorem afterSelection_work (N : ℕ) (selected : UniformSelectionWork.Selected (N + 2)) :
    (afterSelection N selected).work ≤ 34 * (N + 2) + 200 := by
  unfold afterSelection
  split
  · dsimp only
    omega
  · rename_i j hj a hselected
    have hp := UniformPreparedWork.work_le a
    have hi := UniformInitialWork.active_work a.controller N
    have hc := clock_work (N + 2)
    dsimp only
    omega

/-- The total uniform buildr, including explicit fixed-order fallback
for inputs that admit no positive stage. -/
def build : (n : ℕ) → Result (Program n)
  | 0 => ⟨fixed 0 rfl, 5⟩
  | 1 => ⟨fixed 1 rfl, 5⟩
  | N + 2 =>
    let selected := UniformSelectionWork.choose (N + 2)
    let program := afterSelection N selected.value
    ⟨program.value, selected.work + program.work + 4⟩

def initialBound (n : ℕ) : ℕ := UniformSelectionWork.polynomial n + 34 * n + 210

theorem build_work : ∀ n, (build n).work ≤ initialBound n
  | 0 => by unfold build initialBound; dsimp only; omega
  | 1 => by unfold build initialBound; dsimp only; omega
  | N + 2 => by
    have hs := UniformSelectionWork.work_polynomial (N + 2)
    have hp := afterSelection_work N (UniformSelectionWork.choose (N + 2)).value
    change (UniformSelectionWork.choose (N + 2)).work +
      (afterSelection N (UniformSelectionWork.choose (N + 2)).value).work + 4 ≤ _
    unfold initialBound
    omega

theorem strategy_eq (n : ℕ) : (build n).value.machine.strategy = UniformAdversary.strategy n :=
  (build n).value.actual

theorem step_work_le (n : ℕ) (state : (build n).value.machine.State) (query : Query n) :
    ((build n).value.step state query).work ≤ queryBound n :=
  (build n).value.step_work state query

theorem queryBound_polynomial (n : ℕ) : queryBound n ≤ 4000000000000 * (n + 1) ^ 16 := by
  have h := UniformRoutingWork.bound_polynomial n
  unfold queryBound MeasuredController.stepBound
  calc
    UniformRoutingWork.bound n + RankWork.workBound n 2 + 40 ≤
        3000000000000 * (n + 1) ^ 16 + RankWork.workBound n 2 + 40 := by omega
    _ ≤ 4000000000000 * (n + 1) ^ 16 := by
      unfold RankWork.workBound
      ring_nf
      gcongr <;> norm_num

theorem initialization_polynomial (n : ℕ) :
    (build n).work ≤ 10000 * (UniformStage.recipeSize + 1) * (n + 1) ^ 2 := by
  apply (build_work n).trans
  unfold initialBound UniformSelectionWork.polynomial
  nlinarith [Nat.zero_le (UniformStage.recipeSize * n ^ 2), Nat.zero_le (UniformStage.recipeSize * n)]

theorem per_query_polynomial (n : ℕ) (state : (build n).value.machine.State) (query : Query n) :
    ((build n).value.step state query).work ≤ 4000000000000 * (n + 1) ^ 16 :=
  (step_work_le n state query).trans (queryBound_polynomial n)

end SortingAdversary.Optimal.UniformMachineWork
