import SortingAdversary.Continuous.PolylogSchedule
import SortingAdversary.Continuous.PolylogFreeze

/-!
# Online comparison, the finite horizon, and local frozen answers

An active comparison policy supplies the next geometric memory. A countdown
tracks the remaining active calls. At its first subsequent query the machine
keeps that same memory and enters the frozen phase. Each frozen answer uses
the lower-wall comparison rule and the predecessor lists of the frozen graph.

The policy contract concerns one active transition. The transcript lower
bound, the existence of a single compatible ranking for every frozen
continuation, and optimality against every correct decision tree follow below.
-/

namespace SortingAdversary.Continuous.PolylogMachine

open Controller
variable {n : ℕ}

structure Policy (n : ℕ) where
  compare : ℕ → Memory n → Query n → Result n
  parents : Memory n → Fin n → List (Fin n)

structure Policy.Valid (p : Policy n) : Prop where
  compare_step : ∀ k, 64 ≤ k → ∀ M, ActiveInvariant k M → ∀ q,
    ActiveInvariant k (p.compare k M q).memory ∧
      (p.compare k M q).memory.history = ⟨q, (p.compare k M q).answer⟩ :: M.history
  parents_correct : ∀ M x y, x ∈ p.parents M y ↔ M.tree.system.edge x y = true

inductive State (n : ℕ) where
  | fallback
  | active (remaining : ℕ) (memory : Memory n)
  | frozen (memory : Memory n)

def start (n k : ℕ) : State n :=
  if 64 ≤ k then .active (horizon n) (initial n) else .fallback

def Policy.frozenAnswer (p : Policy n) (k : ℕ) (M : Memory n) (q : Query n) : Answer :=
  PolylogFreeze.answer M.tree (fun x => (PolylogFreeze.height (p.parents M) (2^k) x).value) q

def Policy.step (p : Policy n) (k : ℕ) : State n → Query n → Answer × State n
  | .fallback, q => (q.outcome (Equiv.refl _), .fallback)
  | .active 0 M, q | .frozen M, q => (p.frozenAnswer k M q, .frozen M)
  | .active (fuel + 1) M, q =>
    let r := p.compare k M q
    (r.answer, .active fuel r.memory)

def Policy.replay (p : Policy n) (k : ℕ) : History n → State n
  | [] => start n k
  | o :: h => (p.step k (p.replay k h) o.query).2

def Policy.strategy (p : Policy n) (k : ℕ) : Strategy n :=
  fun h q => (p.step k (p.replay k h) q).1

/-- Stateful execution uses only the current state at each decision node. -/
def Policy.execute (p : Policy n) (k : ℕ) : DecisionTree n → State n → RunResult n
  | .leaf output, _ => ⟨output, [], 0⟩
  | .compare q left right, s =>
    let r := p.step k s q
    match r.1 with
    | .less =>
      let tail := p.execute k left r.2
      ⟨tail.output, ⟨q, .less⟩ :: tail.observations, tail.comparisons + 1⟩
    | .greater =>
      let tail := p.execute k right r.2
      ⟨tail.output, ⟨q, .greater⟩ :: tail.observations, tail.comparisons + 1⟩

theorem Policy.execute_eq_run (p : Policy n) (k : ℕ) (t : DecisionTree n) (h : History n) :
    p.execute k t (p.replay k h) = t.run (p.strategy k) h := by
  induction t generalizing h with
  | leaf output => rfl
  | compare q left right ihL ihR =>
    cases ha : (p.step k (p.replay k h) q).1 with
    | less =>
      simpa only [Policy.execute, DecisionTree.run, Policy.strategy, ha, Policy.replay] using
        congrArg (fun tail : RunResult n =>
          (⟨tail.output, ⟨q, .less⟩ :: tail.observations, tail.comparisons + 1⟩ : RunResult n))
            (ihL (⟨q, .less⟩ :: h))
    | greater =>
      simpa only [Policy.execute, DecisionTree.run, Policy.strategy, ha, Policy.replay] using
        congrArg (fun tail : RunResult n =>
          (⟨tail.output, ⟨q, .greater⟩ :: tail.observations, tail.comparisons + 1⟩ : RunResult n))
            (ihR (⟨q, .greater⟩ :: h))

def Policy.Sound (p : Policy n) (k : ℕ) : State n → History n → Prop
  | .fallback, h => k < 64 ∧ Compatible (Equiv.refl _) h
  | .active fuel M, h =>
    64 ≤ k ∧ ActiveInvariant k M ∧ M.history = h ∧ fuel + h.length = horizon n
  | .frozen M, h => horizon n ≤ h.length ∧
    ∃ π : Ranking n, Compatible π h ∧ ∀ q, p.frozenAnswer k M q = q.outcome π

theorem Policy.start_sound (p : Policy n) (k : ℕ) : p.Sound k (start n k) [] := by
  unfold start
  split
  · rename_i hk
    exact ⟨hk, initial_activeInvariant hk, rfl, Nat.add_zero _⟩
  · rename_i hk
    exact ⟨lt_of_not_ge hk, compatible_nil _⟩

private theorem extend {π : Ranking n} {h : History n} (hπ : Compatible π h)
    (q : Query n) (a : Answer) (ha : a = q.outcome π) :
    Compatible π (⟨q, a⟩ :: h) := by
  rw [ha]
  exact (compatible_cons _ _ _).mpr ⟨outcome_holds _ _, hπ⟩

theorem Policy.step_sound (p : Policy n) (hp : p.Valid) (k : ℕ)
    (s : State n) (h : History n) (hs : p.Sound k s h) (q : Query n) :
    p.Sound k (p.step k s q).2 (⟨q, (p.step k s q).1⟩ :: h) := by
  cases s with
  | fallback =>
    exact ⟨hs.1, extend hs.2 q _ rfl⟩
  | frozen M =>
    obtain ⟨hclock, π, hπ, same⟩ := hs
    exact ⟨hclock.trans (Nat.le_succ _), π, extend hπ q _ (same q), same⟩
  | active fuel M =>
    obtain ⟨hk, hM, hh, hclock⟩ := hs
    cases fuel with
    | zero =>
      obtain ⟨π, hπ, same⟩ := PolylogFreeze.ready_frozen_ranking M k hM.1
        (p.parents M) (hp.parents_correct M)
      rw [hh] at hπ
      exact ⟨by simp only [List.length_cons]; omega, π, extend hπ q _ (same q), same⟩
    | succ fuel =>
      obtain ⟨hr, hrh⟩ := hp.compare_step k hk M hM q
      exact ⟨hk, hr, by rw [hrh, hh]; rfl, by simp only [List.length_cons]; omega⟩

theorem Policy.follows_sound (p : Policy n) (hp : p.Valid) (k : ℕ)
    {h : History n} (hf : Follows (p.strategy k) h) : p.Sound k (p.replay k h) h := by
  induction hf with
  | nil => exact p.start_sound k
  | @cons h q _ ih => exact p.step_sound hp k (p.replay k h) h ih q

theorem Policy.consistent (p : Policy n) (hp : p.Valid) (k : ℕ) (t : DecisionTree n) :
    ∃ π : Ranking n, Compatible π (t.run (p.strategy k) []).observations := by
  have hf := run_follows (p.strategy k) t [] Follows.nil
  simp only [List.append_nil] at hf
  have hs := p.follows_sound hp k hf
  have hrev : ∃ π : Ranking n, Compatible π (t.run (p.strategy k) []).observations.reverse := by
    cases he : p.replay k (t.run (p.strategy k) []).observations.reverse with
    | fallback => rw [he] at hs; exact ⟨Equiv.refl _, hs.2⟩
    | frozen M =>
      rw [he] at hs
      obtain ⟨_, π, hπ, _⟩ := hs
      exact ⟨π, hπ⟩
    | active fuel M =>
      rw [he] at hs
      obtain ⟨π, hπ⟩ := hs.2.1.compatible
      exact ⟨π, hs.2.2.1 ▸ hπ⟩
  obtain ⟨π, hπ⟩ := hrev
  exact ⟨π, (compatible_reverse _ _).mp hπ⟩

theorem Policy.short_prefix (p : Policy n) (hp : p.Valid) {k : ℕ} (hk : 64 ≤ k)
    {h : History n} (hf : Follows (p.strategy k) h) (hearly : h.length < horizon n) :
    log2 (n.factorial : ℝ) - (1 + prefixOverhead k) * h.length ≤
      log2 (transcriptCount h : ℝ) := by
  have hs := p.follows_sound hp k hf
  cases he : p.replay k h with
  | fallback =>
    rw [he] at hs
    exact False.elim (not_lt_of_ge hk hs.1)
  | frozen M =>
    rw [he] at hs
    exact False.elim (not_lt_of_ge hs.1 hearly)
  | active fuel M =>
    rw [he] at hs
    simpa only [hs.2.2.1] using hs.2.1.prefix hk

theorem optimal (extra : Optimal.CappedArithmetic.Expr)
    (P : ∀ n, Policy n) (hP : ∀ n, (P n).Valid) :
    Optimal.AsymptoticallyOptimal (fun n => (P n).strategy (PolylogSchedule.parameter extra n)) := by
  apply PolylogSchedule.optimal_of_short_prefix extra
  · exact fun n t => (P n).consistent (hP n) _ t
  · exact fun n hk _ hf hearly => (P n).short_prefix (hP n) hk hf hearly

/-- Executable instance using the existing exact comparison routine. Its
predecessor accessor scans all labels. It witnesses the transition contract
and serves as the semantic reference for sparse implementations. -/
def reference (n : ℕ) : Policy n where
  compare k M q := (Controller.compare k M q).getD ⟨M, .less, []⟩
  parents M y := (List.finRange n).filter (fun x => M.tree.system.edge x y)

theorem reference_valid (n : ℕ) : (reference n).Valid where
  compare_step := by
    intro k hk M hM q
    obtain ⟨r, hr, hvalid⟩ := activeInvariant_compare hk (compareGuarantee n k hk) M hM q
    simpa only [reference, hr, Option.getD_some] using
      And.intro hvalid (compare_history k M q r hr)
  parents_correct := by
    intro M x y
    simp [reference]

theorem reference_optimal (extra : Optimal.CappedArithmetic.Expr) :
    Optimal.AsymptoticallyOptimal
      (fun n => (reference n).strategy (PolylogSchedule.parameter extra n)) :=
  optimal extra reference reference_valid

end SortingAdversary.Continuous.PolylogMachine
