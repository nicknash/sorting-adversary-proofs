import SortingAdversary.Optimal.StoredEvolution
import SortingAdversary.Optimal.ControllerRun

/-!
# Immutable node histories through the concrete controller

The executable child search preserves every old node with an actual local
operation history. The returned repair record identifies its real node both
before the query and after the completed query, including all ancestor
wrapping and matrix materialization.
-/

namespace SortingAdversary.Optimal.ControllerEvolution

open PoolState PoolTree.Tree StoredEvolution RecursiveController ControllerMachine

variable {n : ℕ}

theorem record_evolves {p : Parameters} (record : RepairRecord p n) :
    Evolves (StoredRepair.node record.identity record.before record.children) record.final := by
  have first := Evolves.stopNode record.identity record.before.pool
    ⟨record.before.rows, record.before.order⟩ record.children record.first record.second
    record.first_member record.second_member record.distinct record.updated
  exact first.trans (replayTrace_evolves record.identity record.result.trace record.children
    record.wellFormed record.coherent record.counter)

structure Outcome {p : Parameters} {tree : StoredTree n} {a b : Fin n}
    (answer : StoredRouting.Answered (ready p) (RepairRecord p n) tree a b) : Prop where
  evolves : Evolves tree answer.next
  before : NodeAt tree answer.payload.identity answer.payload.before
  after : NodeAt answer.next answer.payload.identity answer.payload.result.final

theorem stop_spec (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c) (counter : ℕ) :
    Outcome (RecursiveController.stop p t hw ho normal a b ha hb hab hba hstop counter) := by
  cases t with
  | node identity q d children =>
    let result := RecursiveController.stop p (.node identity q d children) hw ho normal
      a b ha hb hab hba hstop counter
    refine ⟨record_evolves result.payload, ?_, ?_⟩
    · exact NodeAt.here identity q d children
    · exact NodeAt.here result.payload.identity result.payload.result.final.pool
        ⟨result.payload.result.final.rows, result.payload.result.final.order⟩ result.payload.replay.children

theorem answerUnknown_spec (p : Parameters) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ) :
    Outcome (answerUnknown p t hw ho normal a b ha hb hab hba counter) := by
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
    next found => exact stop_spec p _ hw ho normal a b ha hb hab hba _ counter
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
      have ih := answerUnknown_spec p child.val.2 (hp.children_ok child' hchild) (ho'.children child' hchild)
        childReady a b hm.1 hm.2 hab' hba' counter
      let first := firstLabel a b result.forward
      let second := secondLabel a b result.forward
      let hf := PoolTree.Tree.first_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hs := PoolTree.Tree.second_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hr := reverse_unknown q a b hab hba result.forward
      refine ⟨?_, NodeAt.descendant child.val child.property ih.before, ?_⟩
      · exact Evolves.delegatedNode identity q d children hp child.val child.property
          first second hf hs hr result.next ih.evolves
      · change NodeAt (StoredRouting.delegatedNode identity q d children hp child.val child.property
          first second hf hs hr result.next) result.payload.identity result.payload.result.final
        unfold StoredRouting.delegatedNode
        apply NodeAt.descendant (child.val.1, result.next)
        · exact List.mem_map.mpr ⟨child.val, child.property, by simp⟩
        · exact ih.after
termination_by sizeOf t
decreasing_by
  subst t
  exact hsize

theorem respond_spec {p : Parameters} (s : Active p n) (q : Query n) :
    Evolves s.tree (respond s q).next.tree ∧
      ∀ record, (respond s q).record = some record →
        NodeAt s.tree record.identity record.before ∧
        NodeAt (respond s q).next.tree record.identity record.result.final := by
  by_cases hl : s.tree.pool.system.edge q.left q.right = true
  · erw [respond, dif_pos hl]
    exact ⟨Evolves.refl _, fun _ h => by contradiction⟩
  · by_cases hg : s.tree.pool.system.edge q.right q.left = true
    · erw [respond, dif_neg hl, dif_pos hg]
      exact ⟨Evolves.refl _, fun _ h => by contradiction⟩
    · let result := answerUnknown p s.tree s.wellFormed s.coherent s.normal q.left q.right
        (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
        hl hg s.counter
      have hs := answerUnknown_spec p s.tree s.wellFormed s.coherent s.normal q.left q.right
        (by rw [s.full]; exact Finset.mem_univ _) (by rw [s.full]; exact Finset.mem_univ _)
        hl hg s.counter
      erw [respond, dif_neg hl, dif_neg hg]
      change Evolves s.tree result.next.materialize ∧ ∀ record, some result.payload = some record →
        NodeAt s.tree record.identity record.before ∧
        NodeAt result.next.materialize record.identity record.result.final
      rw [materialize_eq]
      refine ⟨hs.evolves, ?_⟩
      intro record he
      cases Option.some.inj he
      exact ⟨hs.before, hs.after⟩

theorem respond_evolves {p : Parameters} (s : Active p n) (q : Query n) :
    Evolves s.tree (respond s q).next.tree := (respond_spec s q).1

theorem respond_site {p : Parameters} (s : Active p n) (q : Query n) (record : RepairRecord p n)
    (hrecord : (respond s q).record = some record) :
    NodeAt s.tree record.identity record.before ∧
      NodeAt (respond s q).next.tree record.identity record.result.final :=
  (respond_spec s q).2 record hrecord

theorem activeRun_evolves {p : Parameters} {s final : Active p n} {observations : History n}
    (run : ControllerRun.ActiveRun p s observations final) : Evolves s.tree final.tree := by
  induction run with
  | nil => exact Evolves.refl _
  | cons s q tail ih => exact (respond_evolves s q).trans ih

end SortingAdversary.Optimal.ControllerEvolution
