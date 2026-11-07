import SortingAdversary.Optimal.ControllerMachine
import SortingAdversary.Optimal.UniformController

/-!
# The uniform deterministic adversary family

The bounded stage selector constructs the real controller on every admitted
input size. Small inputs use the fixed label order. The family is total and
legal for every finite comparison tree; its leading-one comparison guarantee
is a separate whole-run accounting theorem.
-/

namespace SortingAdversary.Optimal.UniformAdversary

open PublicLegality

def fixedAnswer {n : ℕ} (q : Query n) : Answer :=
  if q.left < q.right then .less else .greater

def fixedMachine (n : ℕ) : OnlineMachine.Machine n where
  State := Unit
  initial := ()
  step _ q := (fixedAnswer q, ())
  rows _ x y := decide (x ≤ y)
  ordered _ := {
    refl := fun _ => by simp
    trans := fun _ _ _ hxy hyz => decide_eq_true
      (le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
    antisymm := fun _ _ hxy hyx => le_antisymm (of_decide_eq_true hxy) (of_decide_eq_true hyx) }
  monotone _ _ _ _ h := h
  answered _ q := by
    unfold fixedAnswer
    split
    · rename_i h
      exact decide_eq_true h.le
    · rename_i h
      exact decide_eq_true (le_of_not_gt h)

/-- A conservative integer physical clock, of order `n log n`. -/
def cutoff (n : ℕ) : ℕ := 2 * n * (Parameters.logCap n + 1)

def machine : (n : ℕ) → OnlineMachine.Machine n
  | 0 => fixedMachine 0
  | 1 => fixedMachine 1
  | N + 2 =>
      match UniformStage.selectController (N + 2) with
      | none => fixedMachine (N + 2)
      | some p => ControllerMachine.machine p N (cutoff (N + 2))

def strategy (n : ℕ) : Strategy n := (machine n).strategy

/-- Unconditional online legality of the constructed uniform family. -/
theorem consistent : ConsistentFamily strategy := fun n t => (machine n).strategy_consistent t

theorem machine_of_admitted (N : ℕ) (p : RecursiveController.Parameters)
    (h : UniformStage.selectController (N + 2) = some p) :
    machine (N + 2) = ControllerMachine.machine p N (cutoff (N + 2)) := by
  simp only [machine, h]

theorem machine_of_fallback (N : ℕ)
    (h : UniformStage.selectController (N + 2) = none) :
    machine (N + 2) = fixedMachine (N + 2) := by
  simp only [machine, h]

end SortingAdversary.Optimal.UniformAdversary
