import SortingAdversary.Optimal.MeasuredActive
import SortingAdversary.Optimal.BoundedControllerMachine
import SortingAdversary.Optimal.RankWork

/-!
# A measured stateful implementation of the verified strategy

The active phase carries the actual represented tree and a bounded clock.
The freezing transition constructs the exact ranking with measured scans.
Every later answer uses two stored rank reads and a comparison, with no
growing clock or replay of previous queries in the stateful implementation.
-/

namespace SortingAdversary.Optimal.MeasuredController

open RecursiveController RepresentationWork PublicLegality

variable {n cutoff : ℕ} {p : Parameters}

inductive State (p : Parameters) (n cutoff : ℕ) where
  | active (clock : Fin (cutoff + 1)) (state : Active p n)
  | frozen (state : ControllerMachine.Frozen n)

def erase : State p n cutoff → BoundedControllerMachine.State p n cutoff
  | .active clock state => .active clock state.state
  | .frozen state => .frozen state

def frozenAnswer (f : ControllerMachine.Frozen n) (q : Query n) : PrimitiveWork.Result Answer :=
  ⟨if f.ranks[q.left] < f.ranks[q.right] then .less else .greater, 3⟩

@[simp] theorem frozenAnswer_value (f : ControllerMachine.Frozen n) (q : Query n) :
    (frozenAnswer f q).value = f.answer q := rfl

def step (executor : AnswerExecutor p n) (state : State p n cutoff) (q : Query n) :
    PrimitiveWork.Result (Answer × State p n cutoff) :=
  match state with
  | .active clock active =>
    if h : clock.val < cutoff then
      let response := respond executor active q
      ⟨(response.value.answer, .active ⟨clock.val + 1, by omega⟩ response.value.next), response.work + 5⟩
    else
      let frozen := RankWork.frozen active.access.root.publicRow
      let answer := frozenAnswer frozen.value q
      ⟨(answer.value, .frozen frozen.value), frozen.work + answer.work + 5⟩
  | .frozen frozen =>
      let answer := frozenAnswer frozen q
      ⟨(answer.value, .frozen frozen), answer.work + 2⟩

theorem step_actual (executor : AnswerExecutor p n) (state : State p n cutoff) (q : Query n) :
    ((step executor state q).value.1, erase (step executor state q).value.2) =
      BoundedControllerMachine.step (erase state) q := by
  cases state with
  | active clock active =>
    by_cases h : clock.val < cutoff
    · simp only [step, erase, BoundedControllerMachine.step, dif_pos h]
      have ha := (respond executor active q).value.answer_eq
      have hs := (respond executor active q).value.next_eq
      rw [ha, hs]
    · have hrows : RankWork.values active.access.root.publicRow = active.state.tree.pool.system.edge :=
        funext (fun x => funext (active.access.root.publicRow_value x))
      have hf := RankWork.frozen_eq_freeze active.state active.access.root.publicRow hrows
      simp only [step, erase, BoundedControllerMachine.step, dif_neg h, frozenAnswer_value, hf]
  | frozen frozen => rfl

theorem erase_step (executor : AnswerExecutor p n) (state : State p n cutoff) (q : Query n) :
    erase (step executor state q).value.2 = (BoundedControllerMachine.step (erase state) q).2 :=
  congrArg Prod.snd (step_actual executor state q)

theorem step_answer (executor : AnswerExecutor p n) (state : State p n cutoff) (q : Query n) :
    (step executor state q).value.1 = (BoundedControllerMachine.step (erase state) q).1 :=
  congrArg Prod.fst (step_actual executor state q)

def rows (state : State p n cutoff) : SparseClosure.Rows (Fin n) :=
  BoundedControllerMachine.rows (erase state)

def machine (p : Parameters) (N cutoff : ℕ) (executor : AnswerExecutor p (N + 2)) :
    OnlineMachine.Machine (N + 2) where
  State := State p (N + 2) cutoff
  initial := .active ⟨0, Nat.succ_pos _⟩ (Active.initial p N)
  step s q := (step executor s q).value
  rows := rows
  ordered s := ControllerMachine.State.ordered (BoundedControllerMachine.legacy (erase s))
  monotone s q x y h := by
    change BoundedControllerMachine.rows (erase (step executor s q).value.2) x y = true
    rw [erase_step]
    exact (BoundedControllerMachine.machine p N cutoff).monotone (erase s) q x y h
  answered s q := by
    change BoundedControllerMachine.rows (erase (step executor s q).value.2)
      (earlier ⟨q, (step executor s q).value.1⟩) (later ⟨q, (step executor s q).value.1⟩) = true
    rw [erase_step, step_answer]
    exact (BoundedControllerMachine.machine p N cutoff).answered (erase s) q

theorem replay_erase (p : Parameters) (N cutoff : ℕ) (executor : AnswerExecutor p (N + 2))
    (past : History (N + 2)) :
    erase ((machine p N cutoff executor).replay past) =
      (BoundedControllerMachine.machine p N cutoff).replay past := by
  induction past with
  | nil => rfl
  | cons observation past ih =>
    rw [OnlineMachine.Machine.replay_cons, OnlineMachine.Machine.replay_cons]
    change erase (step executor ((machine p N cutoff executor).replay past) observation.query).value.2 = _
    exact (erase_step executor _ _).trans
      (congrArg (fun state => (BoundedControllerMachine.step state observation.query).2) ih)

theorem strategy_eq (p : Parameters) (N cutoff : ℕ) (executor : AnswerExecutor p (N + 2)) :
    (machine p N cutoff executor).strategy = (ControllerMachine.machine p N cutoff).strategy := by
  apply Eq.trans _ (BoundedControllerMachine.strategy_eq p N cutoff)
  funext past query
  change (step executor ((machine p N cutoff executor).replay past) query).value.1 = _
  exact (step_answer executor _ _).trans
    (congrArg (fun state => (BoundedControllerMachine.step state query).1)
      (replay_erase p N cutoff executor past))

def stepBound (n answerWork : ℕ) : ℕ := answerWork + RankWork.workBound n 2 + 40

theorem step_work_le (executor : AnswerExecutor p n) (bound : ℕ) (hbound : AnswerBound executor bound)
    (state : State p n cutoff) (q : Query n) : (step executor state q).work ≤ stepBound n bound := by
  cases state with
  | active clock active =>
    have hr := respond_work_le executor bound hbound active q
    have hf := RankWork.frozen_work_le active.access.root.publicRow 2
      (active.access.root_bound active.cached).publicRow
    by_cases h : clock.val < cutoff
    · simp only [step, dif_pos h]
      unfold stepBound
      omega
    · simp only [step, dif_neg h, frozenAnswer]
      unfold stepBound
      omega
  | frozen frozen =>
    simp only [step, frozenAnswer, stepBound]
    omega

@[simp] theorem frozen_step_work (executor : AnswerExecutor p n) (f : ControllerMachine.Frozen n)
    (q : Query n) : (step executor (.frozen (cutoff := cutoff) f) q).work = 5 := rfl

end SortingAdversary.Optimal.MeasuredController
