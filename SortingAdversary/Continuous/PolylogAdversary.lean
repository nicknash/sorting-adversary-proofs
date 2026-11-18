import SortingAdversary.Continuous.PolylogMachine
import SortingAdversary.Continuous.PolylogOracle
import SortingAdversary.Continuous.PolylogRepair
import SortingAdversary.Continuous.ControllerWork

/-!
# The rounded online adversary

The two rounded local rules can choose different branches and different
anchors from the original controller. Their certificates instantiate the
same selection, repair and accounting proofs. The countdown, outward
enclosures, prefix fallback, and lower-wall frozen order in this strategy
are all executable definitions.
-/

namespace SortingAdversary.Continuous.PolylogAdversary

open Controller
open Optimal (AsymptoticallyOptimal ConsistentFamily)
open Optimal.CappedArithmetic (Expr)

local instance roundedChoices (n : ℕ) : Choices n := PolylogOracle.choices n
local instance roundedLaws (n : ℕ) : ChoiceLaws (roundedChoices n) := PolylogOracle.choices_valid n
local instance roundedLabels (n : ℕ) : ChoiceLabels (roundedChoices n) := PolylogOracle.choices_labels n

/-- Semantic policy. The predecessor list specifies exactly the adjacency
row that the frozen computation reads from the sparse representation. -/
def policy (n : ℕ) : PolylogMachine.Policy n where
  compare k M q := (Controller.compare k M q).getD ⟨M, .less, []⟩
  parents M y := (List.finRange n).filter fun x => M.tree.system.edge x y

theorem policy_valid (n : ℕ) : (policy n).Valid where
  compare_step := by
    intro k hk M hM q
    obtain ⟨r, hr, hready, hvalid⟩ := compare_total_spec k hk M hM.1 q
    have hinv : ActiveInvariant k r.memory :=
      ⟨hready, compare_supported k (by omega) M hM.2.1 q r hr,
        hM.2.2.compare q r hr hvalid⟩
    simpa only [policy, hr, Option.getD_some] using And.intro hinv (compare_history k M q r hr)
  parents_correct := by simp [policy]

abbrev extra : Expr := PolylogRepair.repairRecipe

/-- A single fixed stage recipe for all input sizes. -/
def parameter := PolylogSchedule.parameter extra

def strategy (n : ℕ) : Strategy n := (policy n).strategy (parameter n)

theorem consistent : ConsistentFamily strategy :=
  fun n t => (policy n).consistent (policy_valid n) _ t

theorem asymptoticallyOptimal : AsymptoticallyOptimal strategy :=
  PolylogMachine.optimal extra policy policy_valid

theorem execute_eq_run (n : ℕ) (t : DecisionTree n) :
    (policy n).execute (parameter n) t (PolylogMachine.start n (parameter n)) =
      t.run (strategy n) [] :=
  (policy n).execute_eq_run (parameter n) t []

/-- Composition bound for an active query in the stored representation.
The component budget refers to the actual selection and repair calls
taken on this input. Its units are those of the supplied counted routines. -/
theorem active_work {n : ℕ} (R : ControllerWork.Routines n (parameter n))
    (hk : 64 ≤ parameter n) (s : R.State) (q : Query n) (b : ℕ)
    (hc : ControllerWork.CompareBudget R b s q) :
    (ControllerWork.compare R s q).work ≤ (Optimal.Parameters.logCap n + 7) * (2*b+3) + 5 := by
  apply (ControllerWork.compare_work_height R _ _ _ hc).trans
  have h := PolylogSchedule.height_le (extra := extra) hk
  have hH : 2 ^ parameter n ≤ Optimal.Parameters.logCap n :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ (parameter n))).trans h
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right hH _)) _

end SortingAdversary.Continuous.PolylogAdversary
