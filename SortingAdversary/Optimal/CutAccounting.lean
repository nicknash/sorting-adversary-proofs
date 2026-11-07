import SortingAdversary.Optimal.StoredRowPotential
import SortingAdversary.Optimal.RepairCuts
import SortingAdversary.Optimal.ControllerRun

/-!
# Every actual query pays for its emitted cuts

The proof follows the implemented recursive router. Only its stopping node
inserts an active row; delegations, child admissions and materialization
preserve all other contributions to the exact stored-row potential.
-/

namespace SortingAdversary.Optimal.CutAccounting

open PoolState WidthRepair PoolTree.Tree RecursiveController ControllerMachine
open StoredRowPotential RepairPricing

variable {n : ℕ}

def recordCuts {p : Parameters} (record : RepairRecord p n) : ℕ :=
  (Summary.fromEvents p.repair record.result.events).cuts

def optionCuts {p : Parameters} (record : Option (RepairRecord p n)) : ℕ :=
  match record with | none => 0 | some r => recordCuts r

theorem record_budget {p : Parameters} (record : RepairRecord p n) :
    recordCuts record + rows record.final ≤
      rows (StoredRepair.node record.identity record.before record.children) + 1 := by
  have hcut := Summary.fromEvents_cut_budget p.repair record.result.events
  have hadd := added_rows_le record.before.pool ⟨record.before.rows, record.before.order⟩
    record.first record.second record.first_member record.second_member record.distinct record.updated
  have hchildren := replayTrace_children record.identity record.result.trace record.children
    record.wellFormed record.coherent record.counter
  unfold RepairRecord.final RepairRecord.replay
  simp only [StoredRepair.node, rows]
  rw [hchildren]
  change recordCuts record + ((SparseRepairGraph.rawRows record.result.final.rows.active).card + _) ≤ _
  change (SparseRepairGraph.rawRows
    (compared record.before record.first record.second record.first_member record.second_member
      record.distinct record.updated).rows.active).card ≤
      (SparseRepairGraph.rawRows record.before.rows.active).card + 1 at hadd
  unfold recordCuts
  omega

theorem stop_budget (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) (counter : ℕ) :
    let answer := RecursiveController.stop p t hw ho normal a b ha hb hab hba hstop counter
    recordCuts answer.payload + rows answer.next ≤ rows t + 1 := by
  cases t with
  | node identity q d children =>
    exact record_budget (RecursiveController.stop p (.node identity q d children)
      hw ho normal a b ha hb hab hba hstop counter).payload

theorem answerUnknown_budget (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ) :
    let answer := answerUnknown p t hw ho normal a b ha hb hab hba counter
    recordCuts answer.payload + rows answer.next ≤ rows t + 1 := by
  cases t with
  | node identity q d children =>
    have hw' : (PoolTree.Tree.node identity q (StoredTree.erasedChildren children)).WellFormed := by
      simpa only [StoredTree.erase, StoredTree.erasedChildren] using hw
    have ho' : (PoolTree.Tree.node identity q (StoredTree.erasedChildren children)).Coherent := by
      simpa only [StoredTree.erase, StoredTree.erasedChildren] using ho
    let hp := parts hw'
    unfold answerUnknown
    erw [StoredRouting.routeUnknown.eq_1]
    split
    next found => exact stop_budget p _ hw ho normal a b ha hb hab hba _ counter
    next child found =>
      let hm := StoredRouting.commonChild_members found
      let child' := StoredRouting.semanticChild child.val
      have hchild : child' ∈ StoredTree.erasedChildren children := StoredRouting.semanticChild_mem child.property
      have hab' : child.val.2.pool.system.edge a b ≠ true := by
        rw [← StoredTree.erase_pool child.val.2]
        change child'.2.pool.system.edge a b ≠ true
        rw [ho'.restriction child' hchild a (by simpa [child'] using hm.1) b (by simpa [child'] using hm.2)]
        exact hab
      have hba' : child.val.2.pool.system.edge b a ≠ true := by
        rw [← StoredTree.erase_pool child.val.2]
        change child'.2.pool.system.edge b a ≠ true
        rw [ho'.restriction child' hchild b (by simpa [child'] using hm.2) a (by simpa [child'] using hm.1)]
        exact hba
      let childReady := ((StoredRouting.allNodes_node (ready p) identity q d children).mp normal).2
        child.val child.property
      let result := answerUnknown p child.val.2 (hp.children_ok child' hchild) (ho'.children child' hchild)
        childReady a b hm.1 hm.2 hab' hba' counter
      have hsize : sizeOf child.val.2 < sizeOf (StoredTree.node identity q d children) := by
        have hh := List.sizeOf_lt_of_mem child.property
        rcases child with ⟨⟨key, subtree⟩, hm⟩
        simp only [Prod.mk.sizeOf_spec] at hh
        simp only [StoredTree.node.sizeOf_spec]
        omega
      have ih := answerUnknown_budget p child.val.2 (hp.children_ok child' hchild) (ho'.children child' hchild)
        childReady a b hm.1 hm.2 hab' hba' counter
      let first := firstLabel a b result.forward
      let second := secondLabel a b result.forward
      let hf := PoolTree.Tree.first_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hs := PoolTree.Tree.second_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hr := reverse_unknown q a b hab hba result.forward
      have he := rows_delegatedNode identity q d children hp child.val child.property
        first second hf hs hr result.next
      change recordCuts result.payload +
        rows (StoredRouting.delegatedNode identity q d children hp child.val child.property
          first second hf hs hr result.next) ≤ rows (.node identity q d children) + 1
      change recordCuts result.payload + rows result.next ≤ rows child.val.2 + 1 at ih
      omega
termination_by sizeOf t
decreasing_by
  subst t
  exact hsize

theorem respond_budget {p : Parameters} (s : Active p n) (q : Query n) :
    optionCuts (respond s q).record + rows (respond s q).next.tree ≤ rows s.tree + 1 := by
  by_cases hl : s.tree.pool.system.edge q.left q.right = true
  · erw [respond, dif_pos hl]
    simp only [optionCuts, Nat.zero_add]
    omega
  · by_cases hg : s.tree.pool.system.edge q.right q.left = true
    · erw [respond, dif_neg hl, dif_pos hg]
      simp only [optionCuts, Nat.zero_add]
      omega
    · let result := answerUnknown p s.tree s.wellFormed s.coherent s.normal q.left q.right
        (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
        hl hg s.counter
      have hb := answerUnknown_budget p s.tree s.wellFormed s.coherent s.normal q.left q.right
        (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
        hl hg s.counter
      erw [respond, dif_neg hl, dif_neg hg]
      change recordCuts result.payload + rows result.next.materialize ≤ rows s.tree + 1
      rw [ControllerMachine.materialize_eq]
      exact hb

end SortingAdversary.Optimal.CutAccounting
