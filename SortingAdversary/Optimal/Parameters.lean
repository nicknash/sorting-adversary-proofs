import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Bounded, uniform selection of a parameter stage

The manuscript's uniformization tests consecutive parameter stages, accepting
only stages whose integer requirements fit the available budget. The scan
below is an executable forward scan: it stops at the first failed test, or
when its explicit fuel is exhausted. Stage zero is the fallback policy.

We prove a bound on the number of tests, affordability of the selected stage,
and that the selected stage tends to infinity when every fixed stage eventually
fits. A concrete logarithmic cap is included. The cost function is supplied as
data; no theorem here asserts a running-time bound for evaluating that function
or implements the manuscript's local counting algorithm.
-/

namespace SortingAdversary.Optimal.Parameters

/-- Both outputs of the scan are executable natural numbers. `tests` counts
calls to the supplied affordability predicate, not machine instructions. -/
structure ScanResult where
  stage : ℕ
  tests : ℕ
  deriving DecidableEq, Repr

/-- Test the stages after `start`, in increasing order, at most `fuel` times.
The first unaffordable stage stops the scan immediately. -/
def scanAffordable (cost : ℕ → ℕ) (budget : ℕ) : ℕ → ℕ → ScanResult
  | start, 0 => ⟨start, 0⟩
  | start, fuel + 1 =>
      if cost (start + 1) ≤ budget then
        let rest := scanAffordable cost budget (start + 1) fuel
        ⟨rest.stage, rest.tests + 1⟩
      else
        ⟨start, 1⟩

/-- The scan never moves backwards or beyond its explicit stage cap. -/
theorem scanAffordable_bounds (cost : ℕ → ℕ) (budget start fuel : ℕ) :
    start ≤ (scanAffordable cost budget start fuel).stage ∧
      (scanAffordable cost budget start fuel).stage ≤ start + fuel := by
  induction fuel generalizing start with
  | zero => simp [scanAffordable]
  | succ fuel ih =>
      by_cases h : cost (start + 1) ≤ budget
      · simp only [scanAffordable, if_pos h]
        have hb := ih (start + 1)
        constructor <;> omega
      · simp [scanAffordable, h]

/-- The actual number of affordability tests is at most the supplied fuel. -/
theorem scanAffordable_tests_le (cost : ℕ → ℕ) (budget start fuel : ℕ) :
    (scanAffordable cost budget start fuel).tests ≤ fuel := by
  induction fuel generalizing start with
  | zero => simp [scanAffordable]
  | succ fuel ih =>
      by_cases h : cost (start + 1) ≤ budget
      · simpa only [scanAffordable, if_pos h] using Nat.succ_le_succ (ih (start + 1))
      · simp [scanAffordable, h]

/-- Affordability is preserved, provided the initial stage is affordable. -/
theorem scanAffordable_cost_le (cost : ℕ → ℕ) (budget start fuel : ℕ)
    (hstart : cost start ≤ budget) :
    cost (scanAffordable cost budget start fuel).stage ≤ budget := by
  induction fuel generalizing start with
  | zero => exact hstart
  | succ fuel ih =>
      by_cases h : cost (start + 1) ≤ budget
      · simpa only [scanAffordable, if_pos h] using ih (start + 1) h
      · simpa only [scanAffordable, if_neg h] using hstart

/-- Under monotone requirements, the scan reaches every affordable stage
within its cap. A failed earlier test would contradict that affordability. -/
theorem le_scanAffordable_of_cost_le {cost : ℕ → ℕ} (hcost : Monotone cost)
    (budget start fuel target : ℕ) (hcap : target ≤ start + fuel)
    (haffordable : cost target ≤ budget) :
    target ≤ (scanAffordable cost budget start fuel).stage := by
  induction fuel generalizing start with
  | zero => simpa only [scanAffordable, Nat.add_zero] using hcap
  | succ fuel ih =>
      by_cases h : target ≤ start
      · exact h.trans (scanAffordable_bounds cost budget start (fuel + 1)).1
      · have hnext : cost (start + 1) ≤ budget :=
          (hcost (by omega : start + 1 ≤ target)).trans haffordable
        simpa only [scanAffordable, if_pos hnext] using
          ih (start + 1) (by omega : target ≤ start + 1 + fuel)

/-- If the cap was not reached, the very next stage failed its test.
This property does not need monotonicity of the requirements. -/
theorem scanAffordable_stopped {cost : ℕ → ℕ} {budget start fuel : ℕ}
    (hstop : (scanAffordable cost budget start fuel).stage < start + fuel) :
    budget < cost ((scanAffordable cost budget start fuel).stage + 1) := by
  induction fuel generalizing start with
  | zero => simp [scanAffordable] at hstop
  | succ fuel ih =>
      by_cases h : cost (start + 1) ≤ budget
      · simp only [scanAffordable, if_pos h] at hstop ⊢
        apply ih
        omega
      · simpa only [scanAffordable, if_neg h] using Nat.lt_of_not_ge h

/-- Select a stage for input size `n`, using its specified budget and cap. -/
def selectedStage (cost cap budget : ℕ → ℕ) (n : ℕ) : ℕ :=
  (scanAffordable cost (budget n) 0 (cap n)).stage

theorem selectedStage_le_cap (cost cap budget : ℕ → ℕ) (n : ℕ) :
    selectedStage cost cap budget n ≤ cap n := by
  simpa only [selectedStage, Nat.zero_add] using
    (scanAffordable_bounds cost (budget n) 0 (cap n)).2

theorem selectedStage_cost_le {cost cap budget : ℕ → ℕ} (n : ℕ)
    (hzero : cost 0 ≤ budget n) :
    cost (selectedStage cost cap budget n) ≤ budget n :=
  scanAffordable_cost_le cost (budget n) 0 (cap n) hzero

theorem le_selectedStage {cost cap budget : ℕ → ℕ} (hcost : Monotone cost)
    {n target : ℕ} (hcap : target ≤ cap n) (haffordable : cost target ≤ budget n) :
    target ≤ selectedStage cost cap budget n := by
  exact le_scanAffordable_of_cost_le hcost (budget n) 0 (cap n) target
    (by simpa using hcap) haffordable

/-- The precise "every fixed stage eventually fits" uniformization lemma.
Its assumptions are on finite natural-valued functions. -/
theorem selectedStage_tendsto {cost cap budget : ℕ → ℕ} (hcost : Monotone cost)
    (hcap : Filter.Tendsto cap Filter.atTop Filter.atTop)
    (hbudget : Filter.Tendsto budget Filter.atTop Filter.atTop) :
    Filter.Tendsto (selectedStage cost cap budget) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro target
  obtain ⟨ncap, hncap⟩ := Filter.tendsto_atTop_atTop.mp hcap target
  obtain ⟨nbudget, hnbudget⟩ := Filter.tendsto_atTop_atTop.mp hbudget (cost target)
  refine ⟨max ncap nbudget, ?_⟩
  intro n hn
  exact le_selectedStage hcost
    (hncap n ((le_max_left _ _).trans hn))
    (hnbudget n ((le_max_right _ _).trans hn))

/-- A directly computable cap used for the uniform schedule. -/
def logCap (n : ℕ) : ℕ := Nat.log 2 (n + 1)

theorem logCap_le_input (n : ℕ) : logCap n ≤ n := by
  have h := Nat.log_lt_self 2 (Nat.succ_ne_zero n)
  exact Nat.le_of_lt_succ h

theorem logCap_monotone : Monotone logCap := by
  intro n m h
  exact Nat.log_mono_right (Nat.add_le_add_right h 1)

/-- The explicit threshold `2^target` suffices for the logarithmic cap. -/
theorem le_logCap {target n : ℕ} (hn : 2 ^ target ≤ n) : target ≤ logCap n := by
  exact Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (Nat.le_succ n))

theorem logCap_tendsto : Filter.Tendsto logCap Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro target
  exact ⟨2 ^ target, fun _ hn => le_logCap hn⟩

/-- The more restrictive schedule: both the number of attempted stages and
their supplied integer requirements are capped by `floor(log₂(n+1))`. -/
def logarithmicStage (cost : ℕ → ℕ) (n : ℕ) : ℕ :=
  selectedStage cost logCap logCap n

theorem logarithmicStage_le_cap (cost : ℕ → ℕ) (n : ℕ) :
    logarithmicStage cost n ≤ logCap n :=
  selectedStage_le_cap cost logCap logCap n

theorem logarithmicStage_cost_le {cost : ℕ → ℕ} (hzero : cost 0 = 0) (n : ℕ) :
    cost (logarithmicStage cost n) ≤ logCap n := by
  exact selectedStage_cost_le n (by simp [hzero])

theorem logarithmicStage_tests_le_input (cost : ℕ → ℕ) (n : ℕ) :
    (scanAffordable cost (logCap n) 0 (logCap n)).tests ≤ n :=
  (scanAffordable_tests_le cost (logCap n) 0 (logCap n)).trans (logCap_le_input n)

/-- A fully explicit eventual bound: a fixed stage is reached once the input
dominates the power of two determined by that stage and its finite cost. -/
theorem le_logarithmicStage {cost : ℕ → ℕ} (hcost : Monotone cost)
    {target n : ℕ} (hn : 2 ^ max target (cost target) ≤ n) :
    target ≤ logarithmicStage cost n := by
  have h := le_logCap hn
  apply le_selectedStage hcost
  · exact (le_max_left _ _).trans h
  · exact (le_max_right _ _).trans h

theorem logarithmicStage_tendsto {cost : ℕ → ℕ} (hcost : Monotone cost) :
    Filter.Tendsto (logarithmicStage cost) Filter.atTop Filter.atTop :=
  selectedStage_tendsto hcost logCap_tendsto logCap_tendsto

end SortingAdversary.Optimal.Parameters
