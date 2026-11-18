import SortingAdversary.Continuous.PolylogCached
import SortingAdversary.Continuous.PolylogFrozenQuery
import SortingAdversary.Continuous.PolylogAligned

/-!
# Execution from the stored state

The stage, binary point and table heights are determined once at startup.
Each query receives the current memory and the remaining active-call count.
Replay is used to state the refinement and worst-case work theorems.
-/

namespace SortingAdversary.Continuous.PolylogExecution

open Optimal.PrimitiveWork (Result)
open Optimal.Parameters (logCap)
open PolylogCompare (Memory)
variable {n : ℕ}

structure Config where
  k : ℕ
  depth : ℕ
  binaryPoint : ℕ
  tables : ℕ
  blocks : ℕ
  stageData : PolylogPrepared.Params

def config (n : ℕ) : Config :=
  let k := PolylogAdversary.parameter n
  let D := PolylogSchedule.capacity (logCap n) (ArbitraryLabels.pathHeight k) n
  let P := if 64 ≤ k then PolylogPrepared.Params.stage k else ⟨k,0,0,0,0⟩
  ⟨k, 2^k, D, PolylogResources.tableHeight n, D.size,P⟩

inductive State (n : ℕ) (c : Config) where
  | fallback
  | active (remaining : ℕ) (m : Memory n c.tables c.blocks)
  | frozen (m : Memory n c.tables c.blocks)

def start (n : ℕ) (c : Config) : State n c :=
  if 64 ≤ c.k then .active (Controller.horizon n)
    (PolylogCompare.initialMemory n c.tables c.blocks c.binaryPoint)
  else .fallback

def step (c : Config) : State n c → Query n → Result (Answer × State n c)
  | .fallback, q => ⟨(q.outcome (Equiv.refl _), .fallback), 2⟩
  | .active 0 m, q | .frozen m, q =>
    let a := PolylogFrozenQuery.query m c.depth q
    ⟨(a.value, .frozen m), a.work + 2⟩
  | .active (fuel+1) m, q =>
    let r := PolylogCached.compare c.binaryPoint c.stageData m q
    match r.value with
    | none => ⟨(.less, .active fuel m), r.work+3⟩
    | some (m',a) => ⟨(a, .active fuel m'), r.work+3⟩

private theorem cached_eq {n : ℕ} (hk : 64 ≤ (config n).k)
    (m : Memory n (config n).tables (config n).blocks) (q : Query n) :
    PolylogCached.compare (config n).binaryPoint (config n).stageData m q =
      PolylogCompare.compare (config n).binaryPoint (config n).k m q := by
  have hp : (config n).stageData = PolylogPrepared.Params.stage (config n).k := if_pos hk
  rw [hp, PolylogCached.compare_eq]

private theorem active_work_eq (c : Config) (m : Memory n c.tables c.blocks) (f : ℕ) (q : Query n) :
    (step c (.active (f+1) m) q).work = (PolylogCached.compare c.binaryPoint c.stageData m q).work + 3 := by
  cases h : (PolylogCached.compare c.binaryPoint c.stageData m q).value with
  | none => simp only [step,h]
  | some v => rcases v with ⟨m',a⟩; simp only [step,h]

def replay (c : Config) : History n → State n c
  | [] => start n c
  | o :: h => ((step c (replay c h) o.query).value).2

def strategy (n : ℕ) : Strategy n := fun h q => ((step (config n) (replay (config n) h) q).value).1

def execute (c : Config) : DecisionTree n → State n c → RunResult n
  | .leaf out, _ => ⟨out,[],0⟩
  | .compare q left right, s =>
    let a := (step c s q).value
    match a.1 with
    | .less =>
      let z := execute c left a.2
      ⟨z.output, ⟨q,.less⟩ :: z.observations, z.comparisons + 1⟩
    | .greater =>
      let z := execute c right a.2
      ⟨z.output, ⟨q,.greater⟩ :: z.observations, z.comparisons + 1⟩

theorem execute_eq_run (t : DecisionTree n) (hist : History n) :
    execute (config n) t (replay (config n) hist) = t.run (strategy n) hist := by
  induction t generalizing hist with
  | leaf => rfl
  | compare q l r ihl ihr =>
    cases ha : ((step (config n) (replay (config n) hist) q).value).1 with
    | less =>
      simpa only [execute, DecisionTree.run, strategy, ha, replay] using
        congrArg (fun z : RunResult n =>
          (⟨z.output, ⟨q,.less⟩ :: z.observations, z.comparisons + 1⟩ : RunResult n))
          (ihl (⟨q,.less⟩ :: hist))
    | greater =>
      simpa only [execute, DecisionTree.run, strategy, ha, replay] using
        congrArg (fun z : RunResult n =>
          (⟨z.output, ⟨q,.greater⟩ :: z.observations, z.comparisons + 1⟩ : RunResult n))
          (ihr (⟨q,.greater⟩ :: hist))

abbrev Mem (n : ℕ) := Memory n (config n).tables (config n).blocks

structure Stores (m : Mem n) (M : Controller.Memory n) : Prop where
  aligned : PolylogCompare.Aligned (config n).binaryPoint (logCap n) m M
  ready : Controller.Ready (config n).k M

inductive Relates : State n (config n) → PolylogMachine.State n → Prop where
  | fallback : Relates .fallback .fallback
  | active {m : Mem n} {fuel M} (hk : 64 ≤ (config n).k) (good : Stores m M) :
    Relates (.active fuel m) (.active fuel M)
  | frozen {m : Mem n} {M} (hk : 64 ≤ (config n).k) (good : Stores m M)
      (depth : Controller.totalDepth M ≤ Controller.horizon n) :
    Relates (.frozen m) (.frozen M)

theorem start_relates (n : ℕ) : Relates (start n (config n))
    (PolylogMachine.start n (config n).k) := by
  unfold start PolylogMachine.start
  split
  · rename_i hk
    apply Relates.active hk
    constructor
    · exact PolylogCompare.initialize_aligned _ _ _ _ _ (Nat.lt_size_self _)
    · exact Controller.initial_ready _ _ (by omega)
  · exact .fallback

/-- The active implementation obligation on the states that can be visited
by this driver, including the final query before freezing. -/
def ActiveRefinement (n : ℕ) : Prop :=
  ∀ {hist : History n} {fuel : ℕ} {m : Mem n} {M : Controller.Memory n},
    64 ≤ (config n).k → Stores m M →
    (PolylogAdversary.policy n).replay (config n).k hist = .active (fuel+1) M →
    ∀ q, let r := (PolylogAdversary.policy n).compare (config n).k M q
         ∃ m', (PolylogCompare.compare (config n).binaryPoint (config n).k m q).value =
                some (m',r.answer) ∧ Stores m' r.memory

private theorem frozen_eq {m : Mem n} {M : Controller.Memory n} (hs : Stores m M) (q : Query n) :
    (PolylogFrozenQuery.query m (config n).depth q).value =
      (PolylogAdversary.policy n).frozenAnswer (config n).k M q := by
  obtain ⟨nodes, hr⟩ := hs.aligned.storage
  exact PolylogFrozenQuery.query_eq hr _ _

theorem step_refines (active : ActiveRefinement n) (hist : History n) (q : Query n)
    {s : State n (config n)} {u : PolylogMachine.State n}
    (hs : Relates s u) (hu : (PolylogAdversary.policy n).replay (config n).k hist = u) :
    ((step (config n) s q).value).1 = ((PolylogAdversary.policy n).step (config n).k u q).1 ∧
    Relates ((step (config n) s q).value).2 ((PolylogAdversary.policy n).step (config n).k u q).2 := by
  cases hs with
  | fallback => exact ⟨rfl,.fallback⟩
  | frozen hk good hd => exact ⟨frozen_eq good q,.frozen hk good hd⟩
  | @active m fuel M hk good =>
    cases fuel with
    | zero => exact ⟨frozen_eq good q,.frozen hk good (PolylogResources.replay_refinements hk hist hu)⟩
    | succ f =>
      obtain ⟨m',hr,good'⟩ := active hk good hu q
      simp only [step,cached_eq hk,hr,PolylogMachine.Policy.step]
      exact ⟨True.intro,.active hk good'⟩

theorem replay_relates (active : ActiveRefinement n) (hist : History n) :
    Relates (replay (config n) hist) ((PolylogAdversary.policy n).replay (config n).k hist) := by
  induction hist with
  | nil => exact start_relates n
  | cons o h ih => exact (step_refines active h o.query ih rfl).2

theorem strategy_eq (active : ActiveRefinement n) : strategy n = PolylogAdversary.strategy n := by
  funext h q
  exact (step_refines active h q (replay_relates active h) rfl).1

theorem optimal_of_refinement (active : ∀ n, ActiveRefinement n) :
    Optimal.ConsistentFamily strategy ∧ Optimal.AsymptoticallyOptimal strategy := by
  have he : strategy = PolylogAdversary.strategy := funext fun n => strategy_eq (active n)
  rw [he]
  exact ⟨PolylogAdversary.consistent,PolylogAdversary.asymptoticallyOptimal⟩

/-- An active work estimate may use reachability and the fixed memory
invariants. The driver separately charges the countdown and the frozen branch. -/
def ActiveWork (n B : ℕ) : Prop :=
  ∀ {hist : History n} {fuel : ℕ} {m : Mem n} {M : Controller.Memory n},
    64 ≤ (config n).k → Stores m M →
    (PolylogAdversary.policy n).replay (config n).k hist = .active (fuel+1) M →
    ∀ q, (PolylogCompare.compare (config n).binaryPoint (config n).k m q).work ≤ B

private theorem frozen_work {m : Mem n} {M : Controller.Memory n} (hk : 64 ≤ (config n).k)
    (hs : Stores m M) (hd : Controller.totalDepth M ≤ Controller.horizon n) (q : Query n) :
    (PolylogFrozenQuery.query m (config n).depth q).work ≤ 72000*(logCap n+1)^2 := by
  obtain ⟨nodes, hr⟩ := hs.aligned.storage
  have bits : (config n).blocks ≤ 5+(logCap n+1)*3 :=
    PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) hk le_rfl
  have fit := (PolylogResources.indices_fit hs.aligned.sized bits (by omega)).2
  apply PolylogFrozenQuery.scheduled_work hr hk hs.ready (by rfl) (by omega)
  exact (Nat.le_add_right _ _).trans_lt fit

theorem per_query_of_active (active : ActiveRefinement n) {B : ℕ} (cost : ActiveWork n B)
    (hist : History n) (q : Query n) :
    (step (config n) (replay (config n) hist) q).work ≤ max B (72000*(logCap n+1)^2) + 3 := by
  let u := (PolylogAdversary.policy n).replay (config n).k hist
  have bound {s : State n (config n)} {v : PolylogMachine.State n} (related : Relates s v)
      (hu : u = v) : (step (config n) s q).work ≤ max B (72000*(logCap n+1)^2) + 3 := by
    cases related with
    | fallback => simp only [step]; omega
    | frozen hk good hd =>
      exact (Nat.add_le_add_right (frozen_work hk good hd q) 2).trans (by omega)
    | @active m fuel M hk good =>
      cases fuel with
      | zero =>
        exact (Nat.add_le_add_right (frozen_work hk good (PolylogResources.replay_refinements hk hist hu) q) 2).trans (by omega)
      | succ f =>
        have h := cost hk good hu q
        rw [active_work_eq,cached_eq hk]
        omega
  exact bound (replay_relates active hist) rfl

end SortingAdversary.Continuous.PolylogExecution
