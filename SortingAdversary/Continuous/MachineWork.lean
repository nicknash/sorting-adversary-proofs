import SortingAdversary.Continuous.ControllerWork
import SortingAdversary.Continuous.GraphWork

/-!
# Counted stateful queries and permanent freezing

The active branch composes the measured comparison implementation. Freezing
computes and stores a rank vector, after which each query performs exactly
two rank reads and one comparison. The work bound uses only the bounded
active transcript and the component call certificates for this comparison;
it is independent of the number of later frozen queries.
-/

namespace SortingAdversary.Continuous.MachineWork

open SortingAdversary.Optimal
open ControllerWork

variable {n k : ℕ} (R : Routines n k)

inductive State (R : Routines n k) where
  | active (state : R.State)
  | frozen (ranks : Vector (Fin n) n)

def view : State R → Controller.MachineState n
  | .active s => .active (R.memory s)
  | .frozen ranks => .frozen (fun x => ranks[x])

def answerView (p : Answer × State R) : Answer × Controller.MachineState n :=
  (p.1, view R p.2)

def finish (h : History n) (q : Query n) : PrimitiveWork.Result (Answer × State R) :=
  let ranks := GraphWork.freeze h
  let answer := GraphWork.frozenAnswer ranks.value q
  ⟨(answer.value, .frozen ranks.value), ranks.work + answer.work + 2⟩

theorem finish_value (h : History n) (q : Query n) :
    answerView R (finish R h q).value =
      (Controller.rankAnswer (Controller.freeze h) q, .frozen (Controller.freeze h)) := by
  have hv : (fun x : Fin n => (GraphWork.freeze h).value[x]) = Controller.freeze h := by
    funext x
    rw [GraphWork.freeze_value]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [finish, answerView, view, GraphWork.frozenAnswer_value, hv]

theorem finish_work (h : History n) (q : Query n) (hh : h.length ≤ n ^ 2) :
    (finish R h q).work ≤ 100 * (n + 1) ^ 4 + 5 := by
  have hf := GraphWork.freeze_work_bounded_history h hh
  simp only [finish, GraphWork.frozenAnswer_work]
  omega

/-- The cutoff is computed once by initialization and passed as a stored
natural. Reading the active list's clock is charged by its actual length. -/
def step (cutoff : ℕ) (s : State R) (q : Query n) : PrimitiveWork.Result (Answer × State R) :=
  match s with
  | .frozen ranks =>
    let answer := GraphWork.frozenAnswer ranks q
    ⟨(answer.value, .frozen ranks), answer.work + 1⟩
  | .active s =>
    let clock := (R.memory s).history.length
    if clock < cutoff then
      let compared := ControllerWork.compare R s q
      match compared.value with
      | some (next, a) => ⟨(a, .active next), clock + compared.work + 4⟩
      | none =>
        let frozen := finish R (R.memory s).history q
        ⟨frozen.value, clock + compared.work + frozen.work + 4⟩
    else
      let frozen := finish R (R.memory s).history q
      ⟨frozen.value, clock + frozen.work + 3⟩

theorem step_value (s : State R) (q : Query n) :
    answerView R (step R (Controller.horizon n) s q).value =
      Controller.step k (view R s) q := by
  cases s with
  | frozen ranks => rfl
  | active s =>
    by_cases hc : (R.memory s).history.length < Controller.horizon n
    · have hv := ControllerWork.compare_value R s q
      cases hr : (ControllerWork.compare R s q).value with
      | none =>
        cases he : Controller.compare k (R.memory s) q with
        | none => simp only [step, hc, if_true, hr, finish_value, view, Controller.step, he]
        | some r => simp [hr, he] at hv
      | some z =>
        obtain ⟨t, a⟩ := z
        cases he : Controller.compare k (R.memory s) q with
        | none => simp [hr, he] at hv
        | some r =>
          have hh : R.memory t = r.memory ∧ a = r.answer := by
            simpa only [hr, he, Option.map_some, Option.some.injEq,
              storedView, resultView, Prod.mk.injEq] using hv
          simp only [step, hc, if_true, hr, answerView, view, Controller.step, he, hh.1, hh.2]
    · simp only [step, hc, if_false, finish_value, view, Controller.step]

def QueryBudget (b : ℕ) : State R → Query n → Prop
  | .frozen _, _ => True
  | .active s, q => (R.memory s).history.length ≤ n ^ 2 ∧
      ((R.memory s).history.length < Controller.horizon n → CompareBudget R b s q)

theorem step_work (b : ℕ) (s : State R) (q : Query n) (h : QueryBudget R b s q) :
    (step R (Controller.horizon n) s q).work ≤
      (n + 7) * (2 * b + 3) + 100 * (n + 1) ^ 4 + n ^ 2 + 14 := by
  cases s with
  | frozen ranks =>
    simp only [step, GraphWork.frozenAnswer_work]
    omega
  | active s =>
    have hh := h.1
    have hf := finish_work R (R.memory s).history q hh
    by_cases hc : (R.memory s).history.length < Controller.horizon n
    · have hb := ControllerWork.compare_work R b s q (h.2 hc)
      cases hr : (ControllerWork.compare R s q).value with
      | none => simp only [step, if_pos hc, hr]; omega
      | some z => cases z; simp only [step, if_pos hc, hr]; omega
    · simp only [step, if_neg hc]
      omega

def replay (initial : State R) (past : History n) : State R :=
  past.reverse.foldl (fun s o => (step R (Controller.horizon n) s o.query).value.2) initial

theorem replay_value (initial : State R) (hi : view R initial = Controller.start n k)
    (past : History n) : view R (replay R initial past) = Controller.replay k past := by
  induction past with
  | nil => exact hi
  | cons o past ih =>
    have hm : replay R initial (o :: past) =
        (step R (Controller.horizon n) (replay R initial past) o.query).value.2 := by
      simp [replay, List.foldl_append]
    rw [hm, Controller.replay_cons]
    have hv := congrArg Prod.snd (step_value R (replay R initial past) o.query)
    simpa only [answerView, ih] using hv

end SortingAdversary.Continuous.MachineWork
