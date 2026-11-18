import SortingAdversary.Continuous.PolylogStartup
import SortingAdversary.Continuous.PolylogTrieCharges
import SortingAdversary.Continuous.PolylogCompareComplexity
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

/-- Start from the measured initialization, and keep only the current state
while walking the sorter's decision tree. -/
def run (n : ℕ) (t : DecisionTree n) : RunResult n :=
  let boot := (PolylogStartup.build n).value
  PolylogExecution.execute boot.1 t boot.2

theorem run_eq (n : ℕ) (t : DecisionTree n) :
    run n t = t.run (PolylogExecution.strategy n) [] := by
  rw [run, PolylogStartup.build_value]
  exact PolylogExecution.execute_eq_run t []

/-- Worst-case work for a single query after any history. Replay names
the state reached so far and does not contribute to this query's work. -/
theorem per_query (n : ℕ) (hist : History n) (q : Query n) :
    (PolylogExecution.step (config n) (PolylogExecution.replay (config n) hist) q).work ≤
      20000003 * (Optimal.Parameters.logCap n + 1)^9 := by
  let L := Optimal.Parameters.logCap n+1
  have ha : PolylogExecution.ActiveWork n (20000000*L^9) := by
    intro _ _ m M hk hs _ query
    exact PolylogCompareWork.active_query_polylog (n := n) hk m M hs.ready hs.aligned query
  have run := PolylogExecution.per_query_of_active (active_refinement n) ha hist q
  have pos : 1 ≤ L := Nat.le_add_left 1 _
  have mono : L^2 ≤ L^9 := Nat.pow_le_pow_right pos (by decide)
  have power : 1 ≤ L^9 := Nat.one_le_pow 9 L pos
  change _ ≤ 20000003*L^9
  apply run.trans
  change max (20000000*L^9) (72000*L^2)+3 ≤ _
  omega

theorem stored_entries (n : ℕ) (hist : History n) :
    PolylogExecution.storedEntries (PolylogExecution.replay (config n) hist) ≤
      8210*(n+1)*(Optimal.Parameters.logCap n+1)^4 :=
  PolylogExecution.replay_entries (active_refinement n) hist

/-- Cumulative allocation of persistent trie and adjacency-list cells,
including obsolete versions through any continuation. -/
theorem allocated_storage_cells (n : ℕ) (hist : History n) :
    PolylogTrieCharges.allocatedCells (config n) hist ≤ 8*(PolylogResources.tableHeight n+1) +
      20000003*n*(Optimal.Parameters.logCap n+1)^10 :=
  PolylogTrieCharges.allocated_cells_polynomial (active_refinement n) 20000003 9 (per_query n) hist

/-- One deterministic implementation has both the leading-one comparison
bound and a uniform polylogarithmic worst-case query bound in the
counted-operation model. Both clauses refer to the same state transition. -/
theorem asymptoticallyOptimal_and_polylogarithmic :
    Optimal.AsymptoticallyOptimal PolylogExecution.strategy ∧
      ∀ n, ∀ h : History n, ∀ q : Query n,
        (PolylogExecution.step (config n) (PolylogExecution.replay (config n) h) q).work ≤
          20000003*(Optimal.Parameters.logCap n+1)^9 :=
  ⟨asymptoticallyOptimal, per_query⟩

end SortingAdversary.Continuous.PolylogEfficient
