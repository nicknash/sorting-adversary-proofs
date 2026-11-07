import SortingAdversary.Optimal.CappedArithmetic

/-!
# Bounded stage search using the actual capped evaluator

The scan evaluates a fixed arithmetic recipe at consecutive stage indices.
Both the number of attempts and every arithmetic operation of a rejected
attempt are bounded. Reference requirements occur only in proofs, including
the argument that every fixed prefix of stages is eventually accepted.
-/

namespace SortingAdversary.Optimal.CappedStageScan

open CappedArithmetic Parameters

structure Result where
  stage : ℕ
  tests : ℕ
  work : ℕ
  peak : ℕ
  deriving Repr

def scan (e : Expr) (cap : ℕ) : ℕ → ℕ → Result
  | start, 0 => ⟨start, 0, 0, 0⟩
  | start, fuel + 1 =>
    let trial := e.eval cap (start + 1)
    if trial.value.isSome then
      let rest := scan e cap (start + 1) fuel
      ⟨rest.stage, rest.tests + 1, trial.work + rest.work + 1, max trial.peak rest.peak⟩
    else ⟨start, 1, trial.work + 1, trial.peak⟩

theorem scan_bounds (e : Expr) (cap start fuel : ℕ) :
    start ≤ (scan e cap start fuel).stage ∧ (scan e cap start fuel).stage ≤ start + fuel := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
    rw [scan]
    dsimp only
    split
    · have h := ih (start + 1)
      dsimp only
      omega
    · dsimp only
      omega

theorem scan_tests (e : Expr) (cap start fuel : ℕ) : (scan e cap start fuel).tests ≤ fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    rw [scan]
    dsimp only
    split
    · exact Nat.add_le_add_right (ih _) 1
    · dsimp only; omega

theorem scan_supported (e : Expr) (cap start fuel : ℕ) (hcap : 1 ≤ cap) :
    (scan e cap start fuel).stage = start ∨ e.need (scan e cap start fuel).stage ≤ cap := by
  induction fuel generalizing start with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    rw [scan]
    dsimp only
    split
    · rename_i htrial
      have hneed := (e.eval_isSome cap (start + 1) hcap).mp htrial
      rcases ih (start + 1) with heq | hlast
      · apply Or.inr
        change e.need (scan e cap (start + 1) fuel).stage ≤ cap
        rw [heq]
        exact hneed
      · exact Or.inr hlast
    · exact Or.inl rfl

theorem scan_work (e : Expr) (cap start fuel : ℕ) (hcap : 1 ≤ cap) :
    (scan e cap start fuel).work ≤ fuel * (e.nodes * (5 * (cap + 1) + 2) + 1) := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
    have ht := e.eval_work cap (start + 1) hcap
    have hr := ih (start + 1)
    rw [scan]
    dsimp only
    split <;> dsimp only <;> nlinarith

theorem scan_peak (e : Expr) (cap start fuel M : ℕ) (hcap : 1 ≤ cap)
    (hstart : start + fuel ≤ cap) (hM : e.literalMax ≤ M) :
    (scan e cap start fuel).peak ≤ (cap + M + 1) ^ 2 := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
    have ht := e.eval_peak cap (start + 1) M hcap (by omega) hM
    have hr := ih (start + 1) (by omega)
    rw [scan]
    dsimp only
    split
    · exact max_le ht hr
    · exact ht

/-- A finite prefix envelope used only to prove eventual admission. -/
def prefixNeed (e : Expr) : ℕ → ℕ
  | 0 => 0
  | j + 1 => max (prefixNeed e j) (e.need (j + 1))

theorem prefixNeed_mono (e : Expr) : Monotone (prefixNeed e) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_max_left _ _

theorem need_le_prefix (e : Expr) {j target : ℕ} (hj : 0 < j) (hjt : j ≤ target) :
    e.need j ≤ prefixNeed e target := by
  have h : e.need j ≤ prefixNeed e j := by
    cases j with
    | zero => omega
    | succ j => exact le_max_right _ _
  exact h.trans (prefixNeed_mono e hjt)

theorem reaches_prefix (e : Expr) (cap start fuel target : ℕ) (hcap : 1 ≤ cap)
    (hf : target ≤ start + fuel) (hneed : prefixNeed e target ≤ cap) :
    target ≤ (scan e cap start fuel).stage := by
  induction fuel generalizing start with
  | zero => simpa only [scan, Nat.add_zero] using hf
  | succ fuel ih =>
    by_cases hstart : target ≤ start
    · exact hstart.trans (scan_bounds e cap start (fuel + 1)).1
    · have hj : start + 1 ≤ target := by omega
      have heval : (e.eval cap (start + 1)).value.isSome = true :=
        (e.eval_isSome cap (start + 1) hcap).mpr ((need_le_prefix e (by omega) hj).trans hneed)
      simpa only [scan, heval, Bool.true_eq, ↓reduceIte] using
        ih (start + 1) (by omega : target ≤ start + 1 + fuel)

def select (e : Expr) (n : ℕ) : Result := scan e (logCap n) 0 (logCap n)
def stage (e : Expr) (n : ℕ) : ℕ := (select e n).stage

theorem stage_le (e : Expr) (n : ℕ) : stage e n ≤ logCap n := by
  simpa only [stage, select, Nat.zero_add] using (scan_bounds e (logCap n) 0 (logCap n)).2

theorem tests_le (e : Expr) (n : ℕ) : (select e n).tests ≤ logCap n :=
  scan_tests e (logCap n) 0 (logCap n)

theorem stage_need (e : Expr) (n : ℕ) (hstage : 0 < stage e n) : e.need (stage e n) ≤ logCap n := by
  have hcap : 1 ≤ logCap n := hstage.trans_le (stage_le e n)
  rcases scan_supported e (logCap n) 0 (logCap n) hcap with hzero | hneed
  · change stage e n = 0 at hzero
    omega
  · exact hneed

theorem selected_work (e : Expr) (n : ℕ) :
    (select e n).work ≤ logCap n * (e.nodes * (5 * (logCap n + 1) + 2) + 1) := by
  by_cases hzero : logCap n = 0
  · simp [select, hzero, scan]
  · exact scan_work e _ _ _ (Nat.pos_of_ne_zero hzero)

theorem selected_peak (e : Expr) (n M : ℕ) (hM : e.literalMax ≤ M) :
    (select e n).peak ≤ (logCap n + M + 1) ^ 2 := by
  by_cases hzero : logCap n = 0
  · simp [select, hzero, scan]
  · exact scan_peak e _ _ _ M (Nat.pos_of_ne_zero hzero) (by simp) hM

theorem eventually_reaches (e : Expr) (target n : ℕ)
    (hn : 2 ^ max target (prefixNeed e target) ≤ n) : target ≤ stage e n := by
  by_cases ht : target = 0
  · simp [ht]
  · have hlog := le_logCap hn
    have htarget : target ≤ logCap n := (le_max_left _ _).trans hlog
    have hcap : 1 ≤ logCap n := (Nat.pos_of_ne_zero ht).trans_le htarget
    exact reaches_prefix e _ 0 _ target hcap (by simpa using htarget) ((le_max_right _ _).trans hlog)

theorem stage_tendsto (e : Expr) : Filter.Tendsto (stage e) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro target
  exact ⟨2 ^ max target (prefixNeed e target), fun n hn => eventually_reaches e target n hn⟩

/-- A uniform polynomial in the input size, including failed attempts. The
fixed coefficient is the concrete recipe's syntax size. -/
theorem selected_work_polynomial (e : Expr) (n : ℕ) :
    (select e n).work ≤ n * (e.nodes * (5 * (n + 1) + 2) + 1) := by
  apply (selected_work e n).trans
  exact Nat.mul_le_mul (logCap_le_input n)
    (Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (Nat.add_le_add_right (logCap_le_input n) 1)) 2)) 1)

end SortingAdversary.Optimal.CappedStageScan
