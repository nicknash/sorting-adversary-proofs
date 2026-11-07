import SortingAdversary.Optimal.UniformAdversary

/-!
# A bounded-storage controller with the same transcript strategy

The active clock is bounded by the fixed cutoff. Once a ranking is frozen,
the runtime state contains only that vector and never increments a clock.
The simulation below proves exact equality with the already verified family
against every transcript, including arbitrarily long incorrect sorters.
-/

namespace SortingAdversary.Optimal.BoundedControllerMachine

open RecursiveController ControllerMachine

variable {n : ℕ}

inductive State (p : Parameters) (n cutoff : ℕ) where
  | active (clock : Fin (cutoff + 1)) (state : Active p n)
  | frozen (state : Frozen n)

def legacy {p : Parameters} {cutoff : ℕ} : State p n cutoff → ControllerMachine.State p n
  | .active clock state => ⟨clock.val, .inl state⟩
  | .frozen state => ⟨cutoff + 1, .inr state⟩

def Related {p : Parameters} {cutoff : ℕ} (old : ControllerMachine.State p n) :
    State p n cutoff → Prop
  | .active clock state => old.clock = clock.val ∧ old.mode = .inl state
  | .frozen state => old.mode = .inr state

theorem related_legacy {p : Parameters} {cutoff : ℕ} (state : State p n cutoff) :
    Related (legacy state) state := by cases state <;> simp [Related, legacy]

def step {p : Parameters} {cutoff : ℕ} (state : State p n cutoff) (query : Query n) :
    Answer × State p n cutoff :=
  match state with
  | .active clock active =>
    if h : clock.val < cutoff then
      let response := ControllerMachine.respond active query
      (response.answer, .active ⟨clock.val + 1, by omega⟩ response.next)
    else
      let frozen := ControllerMachine.freeze active
      (frozen.answer query, .frozen frozen)
  | .frozen frozen => (frozen.answer query, .frozen frozen)

theorem step_related {p : Parameters} {cutoff : ℕ}
    (old : ControllerMachine.State p n) (state : State p n cutoff)
    (related : Related old state) (query : Query n) :
    (ControllerMachine.step cutoff old query).1 = (step state query).1 ∧
      Related (ControllerMachine.step cutoff old query).2 (step state query).2 := by
  cases state with
  | active clock active =>
    cases old with
    | mk oldClock mode =>
      obtain ⟨hclock, hmode⟩ := related
      dsimp only at hclock hmode
      cases hclock
      cases hmode
      by_cases h : clock.val < cutoff
      · simp only [ControllerMachine.step, step, if_pos h, dif_pos h, Related, and_self]
      · simp only [ControllerMachine.step, step, if_neg h, dif_neg h, Related, and_self]
  | frozen frozen =>
    cases old with
    | mk oldClock mode =>
      change mode = .inr frozen at related
      cases related
      exact ⟨rfl, rfl⟩

def rows {p : Parameters} {cutoff : ℕ} (state : State p n cutoff) :
    SparseClosure.Rows (Fin n) := (legacy state).rows

theorem related_rows {p : Parameters} {cutoff : ℕ}
    (old : ControllerMachine.State p n) (state : State p n cutoff)
    (related : Related old state) : old.rows = rows state := by
  cases state with
  | active clock active =>
    simp only [rows, legacy, ControllerMachine.State.rows, related.2]
  | frozen frozen =>
    change old.mode = .inr frozen at related
    simp only [rows, legacy, ControllerMachine.State.rows, related]

theorem step_rows {p : Parameters} {cutoff : ℕ} (state : State p n cutoff) (query : Query n) :
    (ControllerMachine.step cutoff (legacy state) query).2.rows = rows (step state query).2 :=
  related_rows _ _ (step_related _ _ (related_legacy state) query).2

theorem step_answer {p : Parameters} {cutoff : ℕ} (state : State p n cutoff) (query : Query n) :
    (ControllerMachine.step cutoff (legacy state) query).1 = (step state query).1 :=
  (step_related _ _ (related_legacy state) query).1

def machine (p : Parameters) (N cutoff : ℕ) : OnlineMachine.Machine (N + 2) where
  State := State p (N + 2) cutoff
  initial := .active ⟨0, Nat.succ_pos _⟩ (initialActive p N)
  step := step
  rows := rows
  ordered s := ControllerMachine.State.ordered (legacy s)
  monotone s q x y h := by
    rw [← step_rows]
    exact ControllerMachine.step_monotone cutoff (legacy s) q x y h
  answered s q := by
    rw [← step_rows, ← step_answer]
    exact ControllerMachine.step_answered cutoff (legacy s) q

theorem replay_related (p : Parameters) (N cutoff : ℕ) (past : History (N + 2)) :
    Related ((ControllerMachine.machine p N cutoff).replay past)
      ((machine p N cutoff).replay past) := by
  induction past with
  | nil => exact ⟨rfl, rfl⟩
  | cons observation past ih =>
    rw [OnlineMachine.Machine.replay_cons, OnlineMachine.Machine.replay_cons]
    exact (step_related _ _ ih observation.query).2

/-- Exact strategy equality; no correctness, length, or cutoff hypothesis
is imposed on the transcript supplied by the caller. -/
theorem strategy_eq (p : Parameters) (N cutoff : ℕ) :
    (machine p N cutoff).strategy = (ControllerMachine.machine p N cutoff).strategy := by
  funext past query
  exact (step_related _ _ (replay_related p N cutoff past) query).1.symm

def clock {p : Parameters} {cutoff : ℕ} : State p n cutoff → ℕ
  | .active value _ => value.val
  | .frozen _ => 0

theorem clock_le {p : Parameters} {cutoff : ℕ} (state : State p n cutoff) : clock state ≤ cutoff := by
  cases state with
  | active value _ => exact Nat.le_of_lt_succ value.isLt
  | frozen _ => exact Nat.zero_le _

@[simp] theorem step_frozen {p : Parameters} {cutoff : ℕ} (f : Frozen n) (q : Query n) :
    step (State.frozen (p := p) (cutoff := cutoff) f) q = (f.answer q, .frozen f) := rfl

end SortingAdversary.Optimal.BoundedControllerMachine

namespace SortingAdversary.Optimal.UniformAdversary

def boundedMachine : (n : ℕ) → OnlineMachine.Machine n
  | 0 => fixedMachine 0
  | 1 => fixedMachine 1
  | N + 2 =>
    match UniformStage.selectController (N + 2) with
    | none => fixedMachine (N + 2)
    | some p => BoundedControllerMachine.machine p N (cutoff (N + 2))

theorem boundedMachine_strategy (n : ℕ) : (boundedMachine n).strategy = strategy n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ N =>
      change (boundedMachine (N + 2)).strategy = strategy (N + 2)
      cases h : UniformStage.selectController (N + 2) with
      | none => simp only [boundedMachine, strategy, machine, h]
      | some p => simpa only [boundedMachine, strategy, machine, h] using
          BoundedControllerMachine.strategy_eq p N (cutoff (N + 2))

end SortingAdversary.Optimal.UniformAdversary
