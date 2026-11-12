import SortingAdversary.Continuous.ControllerCorrect
import SortingAdversary.Continuous.ControllerPrecision
import SortingAdversary.Continuous.ControllerConsequences

/-!
# Resource invariants of the actual bounded controller

Reachability is proved for replay of arbitrary query histories: supplied
answers are ignored, as in the executable machine. Every active state has
at most the prescribed horizon of observations, a valid concrete action
trace, and the precision certificate for its actual stored endpoints and
anchors. The refinement bound is derived from that trace's genuine volumes.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState TraceAccounting Precision UniformStages
open scoped BigOperators

variable {n : ℕ}

def RuntimeInvariant (k : ℕ) (hk : 0 < k) : MachineState n → Prop
  | .active M => 64 ≤ k ∧ ActiveInvariant k M ∧ M.Precise k hk ∧ M.history.length ≤ horizon n
  | .frozen _ => True

theorem start_runtimeInvariant (n k : ℕ) (hk : 0 < k) :
    RuntimeInvariant k hk (start n k) := by
  unfold start
  split
  · rename_i hactive
    exact ⟨hactive, initial_activeInvariant hactive, initial_precise n k hk, Nat.zero_le _⟩
  · trivial

theorem step_runtimeInvariant (k : ℕ) (hk : 0 < k) (s : MachineState n)
    (hs : RuntimeInvariant k hk s) (q : Query n) :
    RuntimeInvariant k hk (step k s q).2 := by
  cases s with
  | frozen ranks => trivial
  | active M =>
    obtain ⟨hactive, hM, hprecise, htime⟩ := hs
    by_cases ht : M.history.length < horizon n
    · obtain ⟨r, hr, hready, hv⟩ := compare_total_spec k hactive M hM.1 q
      simp only [step, if_pos ht, hr]
      refine ⟨hactive, ⟨hready, compare_supported k hk M hM.2.1 q r hr,
        hM.2.2.compare q r hr hv⟩, compare_precise M k hactive hM.1 hprecise q hr, ?_⟩
      rw [compare_history k M q r hr, List.length_cons]
      omega
    · simp only [step, if_neg ht, RuntimeInvariant]

/-- No condition is imposed on the historical answer fields supplied by
a caller. Only the queries determine the actual reachable state. -/
theorem replay_runtimeInvariant (k : ℕ) (hk : 0 < k) (past : History n) :
    RuntimeInvariant k hk (replay k past) := by
  induction past with
  | nil => exact start_runtimeInvariant n k hk
  | cons o past ih =>
    rw [replay_cons]
    exact step_runtimeInvariant k hk _ ih o.query

theorem refinementCount_eq (actions : List (Action n)) :
    refinementCount actions = TraceAccounting.actionRefinements actions := by
  unfold refinementCount TraceAccounting.actionRefinements
  congr 1

theorem Traced.totalDepth_le {k : ℕ} (hk : 64 ≤ k) {M : Memory n}
    (hM : Traced k M) (hgeo : Geometric M) :
    (totalDepth M : ℝ) ≤ 8 * M.history.length / k := by
  obtain ⟨actions, hactions, hvalid⟩ := hM
  have hb := refinements_le hk actions hvalid (by simpa only [hactions] using hgeo)
  have hd := totalDepth_runActions (initial n) actions
  rw [hactions, totalDepth_initial, zero_add, refinementCount_eq] at hd
  simpa only [hactions, ← hd] using hb

/-- The deliberately loose integral bound is convenient for a fixed
polynomial word and bit model; the sharper `8q/k` inequality is above. -/
theorem Traced.totalDepth_le_horizon {k : ℕ} (hk : 64 ≤ k) {M : Memory n}
    (hM : Traced k M) (hgeo : Geometric M) (ht : M.history.length ≤ horizon n) :
    totalDepth M ≤ horizon n := by
  have hb := hM.totalDepth_le hk hgeo
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul : (totalDepth M : ℝ) * k ≤ 8 * M.history.length :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < k)).mp hb
  have hnonneg : (0 : ℝ) ≤ totalDepth M := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left (show (8 : ℝ) ≤ k by linarith) hnonneg
  have hdepth : (totalDepth M : ℝ) ≤ M.history.length := by nlinarith
  exact (by exact_mod_cast hdepth : totalDepth M ≤ M.history.length).trans ht

theorem horizon_le_square (n : ℕ) : horizon n ≤ n ^ 2 := by
  unfold horizon
  have hlog : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  simpa only [pow_two] using Nat.mul_le_mul_left n hlog

theorem active_depth_bound (k : ℕ) (hk : 0 < k) (past : History n)
    (M : Memory n) (h : replay k past = .active M) : totalDepth M ≤ n ^ 2 := by
  have hr := replay_runtimeInvariant k hk past
  rw [h] at hr
  exact (hr.2.1.2.2.totalDepth_le_horizon hr.1 hr.2.1.1.toGeometric hr.2.2.2).trans
    (horizon_le_square n)

theorem active_grid_bound (k : ℕ) (hk : 0 < k) (past : History n)
    (M : Memory n) (h : replay k past = .active M)
    (hE : enumerationBudget k hk ≤ n) : M.OnGrid (n ^ 3) := by
  have hr := replay_runtimeInvariant k hk past
  rw [h] at hr
  have hlog : Nat.log 2 (enumerationBudget k hk) ≤ n :=
    (Nat.log_le_self 2 _).trans hE
  have hd := active_depth_bound k hk past M h
  apply Memory.OnGrid.mono hr.2.2.1
  calc
    totalDepth M * Nat.log 2 (enumerationBudget k hk) ≤ n ^ 2 * n := Nat.mul_le_mul hd hlog
    _ = n ^ 3 := by ring

theorem active_endpoint_bits (k : ℕ) (hk : 0 < k) (past : History n)
    (M : Memory n) (h : replay k past = .active M)
    (hE : enumerationBudget k hk ≤ n) (x : Fin n) :
    Nat.size (M.tree.system.lower x).num.natAbs ≤ n ^ 3 + 1 ∧
    Nat.size (M.tree.system.lower x).den ≤ n ^ 3 + 1 ∧
    Nat.size (M.tree.system.upper x).num.natAbs ≤ n ^ 3 + 1 ∧
    Nat.size (M.tree.system.upper x).den ≤ n ^ 3 + 1 := by
  have hr := replay_runtimeInvariant k hk past
  rw [h] at hr
  have hb := stored_endpoint_bits (active_grid_bound k hk past M h hE) hr.2.1.1.toGeometric x
  exact ⟨hb.2.1, hb.1, hb.2.2.2, hb.2.2.1⟩

end SortingAdversary.Continuous.Controller
