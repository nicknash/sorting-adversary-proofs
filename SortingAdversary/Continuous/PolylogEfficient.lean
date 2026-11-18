import SortingAdversary.Continuous.PolylogExecution
import SortingAdversary.Continuous.PolylogCompareProofs

/-! # Correctness and cost of the stored online adversary -/

namespace SortingAdversary.Continuous.PolylogEfficient

open PolylogExecution (config Mem)
variable {n : ℕ}

set_option maxHeartbeats 1500000 in
/-- Every active call returns a state that represents the rounded policy's
next memory. Feasibility and allocation bounds are propagated to the next
call, including the state that will be frozen. -/
theorem active_refinement (n : ℕ) : PolylogExecution.ActiveRefinement n := by
  intro hist fuel m M hk good hr q
  have depth := PolylogResources.replay_refinements (n := n) (k := (config n).k)
    (M := M) (fuel := fuel+1) hk hist hr
  obtain ⟨u, huv, aligned⟩ := PolylogCompare.compare_aligned (n := n)
    hk m M good.ready good.aligned depth q
  exact ⟨u, huv, aligned, PolylogAdversary.compare_ready (n := n) (k := (config n).k) hk good.ready q⟩

theorem strategy_eq (n : ℕ) : PolylogExecution.strategy n = PolylogAdversary.strategy n :=
  PolylogExecution.strategy_eq (active_refinement n)

theorem consistent : Optimal.ConsistentFamily PolylogExecution.strategy :=
  (PolylogExecution.optimal_of_refinement active_refinement).1

theorem asymptoticallyOptimal : Optimal.AsymptoticallyOptimal PolylogExecution.strategy :=
  (PolylogExecution.optimal_of_refinement active_refinement).2

/-- The comparison lower bound applies directly to a run that only passes
the current memory to the next sorting-tree node. -/
theorem execute_eq_run (n : ℕ) (t : DecisionTree n) :
    PolylogExecution.execute (config n) t (PolylogExecution.start n (config n)) =
      t.run (PolylogAdversary.strategy n) [] := by
  simpa only [strategy_eq, PolylogExecution.replay] using
    PolylogExecution.execute_eq_run t []

end SortingAdversary.Continuous.PolylogEfficient
