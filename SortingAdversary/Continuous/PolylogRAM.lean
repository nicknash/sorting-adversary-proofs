import SortingAdversary.Continuous.PolylogWordBudget
import SortingAdversary.Continuous.PolylogWordProgram
import SortingAdversary.Continuous.PolylogKernelProfile
import SortingAdversary.Continuous.PolylogEfficient

/-!
# The optimal adversary with priced word operations

The active comparison executes the profiled dictionary, graph, dyadic and
rational routines. Frozen queries use the measured predecessor and
dictionary searches. The configuration and initial memory are built once.
-/

namespace SortingAdversary.Continuous.PolylogRAM

open PolylogExecution (Config State config)
open Optimal.Parameters (logCap)
open Optimal.PrimitiveWork (Result)
variable {n : ℕ}

def step (c : Config) : State n c → Query n → Result (Answer × State n c)
  | .active (f+1) m, q =>
    let r := PolylogWordProgram.compare PolylogKernelProfile.kernels c.binaryPoint c.stageData m q
    match r.value with
    | none => ⟨(.less,.active f m), r.work+3⟩
    | some (u,a) => ⟨(a,.active f u), r.work+3⟩
  | s, q => PolylogExecution.step c s q

theorem step_value (c : Config) (s : State n c) (q : Query n) :
    (step c s q).value = (PolylogExecution.step c s q).value := by
  cases s with
  | fallback | frozen => rfl
  | active f m =>
    cases f with
    | zero => rfl
    | succ f =>
      cases hr : (PolylogCached.compare c.binaryPoint c.stageData m q).value with
      | none => simp only [step, PolylogExecution.step, PolylogWordProgram.compare_value PolylogKernelProfile.correct,hr]
      | some r => cases r; simp only [step, PolylogExecution.step, PolylogWordProgram.compare_value PolylogKernelProfile.correct,hr]

private theorem active_step_work (c : Config) (m : PolylogCompare.Memory n c.tables c.blocks)
    (f : ℕ) (q : Query n) :
    (step c (.active (f+1) m) q).work =
      (PolylogWordProgram.compare PolylogKernelProfile.kernels c.binaryPoint c.stageData m q).work+3 := by
  cases hr : (PolylogWordProgram.compare PolylogKernelProfile.kernels c.binaryPoint c.stageData m q).value with
  | none => simp only [step,hr]
  | some r => cases r; simp only [step,hr]

def replay (c : Config) : History n → State n c
  | [] => PolylogExecution.start n c
  | o :: h => (step c (replay c h) o.query).value.2

theorem replay_eq (c : Config) (h : History n) : replay c h = PolylogExecution.replay c h := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [replay,PolylogExecution.replay,ih,step_value]

def strategy (n : ℕ) : Strategy n := fun h q => (step (config n) (replay (config n) h) q).value.1

theorem strategy_eq (n : ℕ) : strategy n = PolylogExecution.strategy n := by
  funext h q
  simp only [strategy,PolylogExecution.strategy,replay_eq,step_value]

/-- A sorter can query this machine by passing forward only the last
returned state. The startup tuple is shared across the whole run. -/
def execute (c : Config) : DecisionTree n → State n c → RunResult n
  | .leaf out, _ => ⟨out,[],0⟩
  | .compare q left right, s =>
    let a := (step c s q).value
    match a.1 with
    | .less =>
      let tail := execute c left a.2
      ⟨tail.output, ⟨q,.less⟩ :: tail.observations,tail.comparisons+1⟩
    | .greater =>
      let tail := execute c right a.2
      ⟨tail.output, ⟨q,.greater⟩ :: tail.observations,tail.comparisons+1⟩

theorem execute_eq (c : Config) (t : DecisionTree n) (s : State n c) :
    execute c t s = PolylogExecution.execute c t s := by
  induction t generalizing s with
  | leaf => rfl
  | compare q l r ihl ihr =>
    cases ha : (PolylogExecution.step c s q).value.1 <;>
      simp only [execute,PolylogExecution.execute,step_value,ha,ihl,ihr]

def run (n : ℕ) (t : DecisionTree n) : RunResult n :=
  let boot := (PolylogStartup.build n).value
  execute boot.1 t boot.2

theorem run_eq (n : ℕ) (t : DecisionTree n) : run n t = t.run (strategy n) [] := by
  rw [run,execute_eq,strategy_eq]
  exact PolylogEfficient.run_eq n t

set_option maxHeartbeats 1200000 in
theorem per_query (n : ℕ) (h : History n) (q : Query n) :
    (step (config n) (replay (config n) h) q).work ≤ (10^20+3)*(logCap n+1)^10 := by
  rw [replay_eq]
  let L := logCap n+1
  have hL : 1 ≤ L := Nat.le_add_left 1 _
  have powPos := Nat.one_le_pow 10 L hL
  have powMono : L^9 ≤ L^10 := Nat.pow_le_pow_right hL (by decide)
  have base := PolylogEfficient.per_query n h q
  change _ ≤ 20000003*L^9 at base
  have rel := PolylogExecution.replay_relates (PolylogEfficient.active_refinement n) h
  generalize hs : PolylogExecution.replay (config n) h = s at rel base ⊢
  generalize hr : (PolylogAdversary.policy n).replay (config n).k h = r at rel
  cases rel with
  | fallback | frozen =>
    apply base.trans
    change 20000003*L^9 ≤ (10^20+3)*L^10
    omega
  | @active m fuel M hk good =>
    cases fuel with
    | zero =>
      apply base.trans
      change 20000003*L^9 ≤ (10^20+3)*L^10
      omega
    | succ f =>
      have depth := PolylogResources.replay_refinements (n := n) (k := (config n).k)
        (M := M) (fuel := f+1) hk h hr
      have hp : (config n).stageData = PolylogPrepared.Params.stage (config n).k := if_pos hk
      rw [active_step_work,hp]
      have bound := (PolylogWordProgram.compare_work PolylogKernelProfile.correct m q).trans
        (PolylogWordCompare.active_work (n := n) hk m M good.ready good.aligned depth q)
      change _ ≤ 10^20*L^10 at bound
      apply (Nat.add_le_add_right bound 3).trans
      change 10^20*L^10+3 ≤ (10^20+3)*L^10
      omega

theorem stored_entries (n : ℕ) (h : History n) :
    PolylogExecution.storedEntries (replay (config n) h) ≤ 8210*(n+1)*(logCap n+1)^4 := by
  rw [replay_eq]
  exact PolylogEfficient.stored_entries n h

/-- Total work in the mutable part of a transcript. Frozen suffixes may
be arbitrarily long and leave the persistent state untouched. -/
def preFreezeWork (c : Config) : History n → ℕ
  | [] => 0
  | o :: h => preFreezeWork c h +
      if h.length < Controller.horizon n then (step c (replay c h) o.query).work else 0

theorem preFreezeWork_bound (n : ℕ) (hist : History n) :
    preFreezeWork (config n) hist ≤ (10^20+3)*n*(logCap n+1)^11 := by
  let B := (10^20+3)*(logCap n+1)^10
  have byLength (h : History n) :
      preFreezeWork (config n) h ≤ min h.length (Controller.horizon n)*B := by
    induction h with
    | nil => simp [preFreezeWork]
    | cons o h ih =>
      by_cases short : h.length < Controller.horizon n
      · simp only [preFreezeWork,if_pos short,List.length_cons,Nat.min_eq_left (Nat.succ_le_of_lt short),
          Nat.succ_mul]
        rw [Nat.min_eq_left short.le] at ih
        exact Nat.add_le_add ih (per_query n h o.query)
      · have done := Nat.le_of_not_gt short
        simpa only [preFreezeWork,if_neg short,Nat.add_zero,List.length_cons,
          Nat.min_eq_right (Nat.le_succ_of_le done)] using (Nat.min_eq_right done ▸ ih)
  apply (byLength hist).trans
  calc
    _ ≤ (n*(logCap n+1))*B := Nat.mul_le_mul_right _
      ((Nat.min_le_right ..).trans (PolylogSchedule.horizon_le n))
    _ = _ := by dsimp only [B]; ring

/-- Both guarantees refer to the same online implementation, at every
input size; the lower bound has its usual asymptotic quantifiers. -/
theorem asymptoticallyOptimal_and_polylogarithmic :
    Optimal.AsymptoticallyOptimal strategy ∧
      ∀ n, ∀ h : History n, ∀ q : Query n,
        (step (config n) (replay (config n) h) q).work ≤ (10^20+3)*(logCap n+1)^10 := by
  have eq : strategy = PolylogExecution.strategy := funext strategy_eq
  exact ⟨by rw [eq]; exact PolylogEfficient.asymptoticallyOptimal,per_query⟩

end SortingAdversary.Continuous.PolylogRAM
