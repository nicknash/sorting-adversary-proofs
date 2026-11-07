import SortingAdversary.Optimal.LedgerRunPrices

/-!
# The factorial ledger potential is the actual child-population credit

Every entered location is a member of its real stored pool. Unique immutable
node identities identify the corresponding finite sums. The root population
is constant during the run, so its factorial term cancels exactly, leaving
one factorial credit for every actual nonroot stored pool.
-/

namespace SortingAdversary.Optimal.TreeFactorialCredit

open scoped BigOperators
open PoolState PoolTree.Tree PoolTreeAccounting PoolTreeTraversal TreeChronology
open LedgerTreeBridge LedgerBirthCredits LedgerRun RecursiveController ControllerMachine ControllerRun

variable {n : ℕ}

noncomputable def treeFactorial (tree : PoolTree.Tree n) : ℝ :=
  ((storedPools tree).map (fun a => Real.log (a.2.members.card.factorial : ℝ))).sum

noncomputable def nonrootFactorial (tree : PoolTree.Tree n) : ℝ :=
  ((storedPools tree).tail.map (fun a => Real.log (a.2.members.card.factorial : ℝ))).sum

theorem treeFactorial_eq_root_add (tree : PoolTree.Tree n) :
    treeFactorial tree = Real.log (tree.pool.members.card.factorial : ℝ) + nonrootFactorial tree := by
  cases tree with
  | node identity p children => simp only [treeFactorial, nonrootFactorial, storedPools, List.tail_cons,
      List.map_cons, List.sum_cons, PoolTree.Tree.pool]

theorem creditNodes_eq_indices (ledger : IncidenceLedger.State n) (tree : PoolTree.Tree n)
    (hw : tree.WellFormed) (hnonempty : tree.pool.members.Nonempty) (hrep : Represents ledger tree) :
    creditNodes ledger = Finset.univ.image (identityAt tree) := by
  ext identity
  constructor
  · intro hi
    obtain ⟨location, hl, he⟩ := Finset.mem_image.mp hi
    rw [hrep.entered] at hl
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (congrArg Prod.fst hx).trans he⟩
  · intro hi
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨x, hx⟩ := storedPools_nonempty hw hnonempty ((storedPools tree).get i) (List.get_mem _ _)
    apply Finset.mem_image.mpr
    refine ⟨(identityAt tree i, x), ?_, rfl⟩
    rw [hrep.entered]
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

theorem factorialCredit_eq_tree (ledger : IncidenceLedger.State n) (tree : PoolTree.Tree n)
    (hw : tree.WellFormed) (hnonempty : tree.pool.members.Nonempty) (counter : ℕ)
    (ha : Allocated tree counter) (hrep : Represents ledger tree) :
    factorialCredit ledger = treeFactorial tree := by
  unfold factorialCredit
  rw [creditNodes_eq_indices ledger tree hw hnonempty hrep, Finset.sum_image]
  · rw [treeFactorial, sum_map_get]
    apply Finset.sum_congr rfl
    intro i _
    have hc := enteredCount_at_pool hrep ha ((storedPools tree).get i) (List.get_mem _ _)
    change enteredCount ledger (identityAt tree i) = (poolAt tree i).members.card at hc
    rw [hc]
    rfl
  · intro i _ j _ he
    exact identityAt_injective ha he

theorem initial_factorialCredit (N : ℕ) :
    factorialCredit (initialLedger N) = Real.log ((N + 2).factorial : ℝ) := by
  have hn : (PoolTree.Tree.initial N).pool.members.Nonempty := by
    change (Finset.univ : Finset (Fin (N + 2))).Nonempty
    exact Finset.univ_nonempty
  rw [factorialCredit_eq_tree (initialLedger N) (PoolTree.Tree.initial N) (initial_wellFormed N)
    hn 1 (TreeChronology.initial_allocated N) (initial_represents N)]
  simp [treeFactorial, storedPools, PoolTree.Tree.initial, initialRoot]

/-- This is exactly the population-factorial credit needed by the final
cheap/hub split, with no receipt destination reconstruction. -/
theorem actual_factorial_difference (p : Parameters) (N : ℕ) {observations : History (N + 2)}
    {final : Active p (N + 2)} (history : ActiveRun p (initialActive p N) observations final) :
    factorialCredit (initialLog p N observations).ledger - factorialCredit (initialLedger N) =
      nonrootFactorial final.tree.erase := by
  have hs := initial_spec p N history
  have hn : final.tree.erase.pool.members.Nonempty := by
    rw [StoredTree.erase_pool, final.full]
    exact Finset.univ_nonempty
  have hc : final.tree.erase.pool.members.card = N + 2 := by
    rw [StoredTree.erase_pool, final.full]
    simp
  have he := factorialCredit_eq_tree (initialLog p N observations).ledger final.tree.erase
    final.wellFormed hn final.counter hs.allocated hs.represents
  rw [he,
    initial_factorialCredit, treeFactorial_eq_root_add, hc]
  ring

end SortingAdversary.Optimal.TreeFactorialCredit
