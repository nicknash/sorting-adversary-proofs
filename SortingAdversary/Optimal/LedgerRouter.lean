import SortingAdversary.Optimal.LedgerQuery

/-!
# The concrete recursive router preserves the global chronological ledger

A physical query creates one record at its actual stopping node. Ancestor
delegations update public relations but add no other incidence record. The
proof follows the executable child search and uses an explicit one-hole tree
context, so allocator freshness is checked against the entire global tree.
-/

namespace SortingAdversary.Optimal.LedgerRouter

open PoolState PoolTree.Tree TreeChronology LedgerTreeBridge LedgerTreeTransitions
open LedgerSourceHistory LedgerStoredHistory LedgerStoredReplay LedgerQuery RecursiveController

variable {n : ℕ}

theorem replaceChildren_split (before after : List (ℕ × PoolTree.Tree n))
    (target : ℕ × PoolTree.Tree n) (next : PoolTree.Tree n)
    (hk : ((before ++ target :: after).map Prod.fst).Nodup) :
    PoolTree.Tree.replaceChildren target.1 next (before ++ target :: after) =
      before ++ (target.1, next) :: after := by
  have hbefore : ∀ a ∈ before, a.1 ≠ target.1 := by
    intro a ha he
    have hnodup := hk
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnodup
    exact hnodup.2.2 a.1 (List.mem_map.mpr ⟨a, ha, rfl⟩) target.1 List.mem_cons_self he
  have hafter : ∀ a ∈ after, a.1 ≠ target.1 := by
    intro a ha he
    have hnodup := hk
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnodup
    exact hnodup.2.1.1 (he ▸ List.mem_map.mpr ⟨a, ha, rfl⟩)
  simp only [PoolTree.Tree.replaceChildren, List.map_append, List.map_cons, ite_true]
  change PoolTree.Tree.replaceChildren target.1 next before ++
    (target.1, next) :: PoolTree.Tree.replaceChildren target.1 next after = _
  rw [PoolTree.Tree.replaceChildren_unchanged _ _ _ hbefore,
    PoolTree.Tree.replaceChildren_unchanged _ _ _ hafter]

theorem answerUnknown_spec (threshold : ℕ) (ctx : Context n) (p : Parameters)
    (hthreshold : threshold ≤ p.repair.D) (t : StoredTree n)
    (hw : t.erase.WellFormed) (ho : t.erase.Coherent)
    (normal : StoredRouting.AllNodes (ready p) t)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true) (counter : ℕ)
    (ledger : IncidenceLedger.State n) (halloc : Allocated (ctx.plug t.erase) counter)
    (hrep : Represents ledger (ctx.plug t.erase)) (hrecorded : Recorded ledger.calls t) :
    Outcome threshold ctx p ledger (answerUnknown p t hw ho normal a b ha hb hab hba counter) := by
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
    next found =>
      exact stop_spec threshold ctx p hthreshold _ hw ho normal a b ha hb hab hba _ counter
        ledger halloc hrep hrecorded
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
      obtain ⟨before, after, hsplit, _⟩ := List.eq_append_cons_of_mem hchild
      let childCtx : Context n := .child identity q before child.val.1 after ctx
      have hplug : childCtx.plug child.val.2.erase =
          ctx.plug (StoredTree.node identity q d children).erase := by
        rw [StoredTree.erase]
        change ctx.plug (.node identity q (before ++ (child.val.1, child.val.2.erase) :: after)) =
          ctx.plug (.node identity q (StoredTree.erasedChildren children))
        rw [hsplit]
        rfl
      have halloc' : Allocated (childCtx.plug child.val.2.erase) counter := by rw [hplug]; exact halloc
      have hrep' : Represents ledger (childCtx.plug child.val.2.erase) := by rw [hplug]; exact hrep
      have hsize : sizeOf child.val.2 < sizeOf (StoredTree.node identity q d children) := by
        have hh := List.sizeOf_lt_of_mem child.property
        rcases child with ⟨⟨key, subtree⟩, hm⟩
        simp only [Prod.mk.sizeOf_spec] at hh
        simp only [StoredTree.node.sizeOf_spec]
        omega
      have ih := answerUnknown_spec threshold childCtx p hthreshold child.val.2
        (hp.children_ok child' hchild) (ho'.children child' hchild) childReady a b hm.1 hm.2 hab' hba'
        counter ledger halloc' hrep' (hrecorded.children child.val child.property)
      have hkeys : ((before ++ child' :: after).map Prod.fst).Nodup := by rw [← hsplit]; exact hp.keys
      have hplugNext : childCtx.plug result.next.erase =
          ctx.plug (.node identity q
            (PoolTree.Tree.replaceChildren child.val.1 result.next.erase (StoredTree.erasedChildren children))) := by
        change ctx.plug (.node identity q (before ++ (child.val.1, result.next.erase) :: after)) = _
        rw [hsplit]
        simpa only [child', StoredRouting.semanticChild] using
          congrArg (fun xs => ctx.plug (.node identity q xs))
            (replaceChildren_split before after child' result.next.erase hkeys).symm
      let first := firstLabel a b result.forward
      let second := secondLabel a b result.forward
      let hf := PoolTree.Tree.first_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hs := PoolTree.Tree.second_member child.val.2.pool a b hm.1 hm.2 result.forward
      let hr := reverse_unknown q a b hab hba result.forward
      refine ⟨ih.accepted, ?_, ?_, ?_, ih.charge, ih.origin⟩
      · change Represents (recordLog result.payload ledger).ledger
          (ctx.plug (StoredRouting.delegatedNode identity q d children hp child.val child.property
            first second hf hs hr result.next).erase)
        rw [StoredRouting.erase_delegatedNode, PoolTree.Tree.delegatedNode]
        refine represents_poolUpdate _ ctx identity q _ _ ?_ ?_ ?_
        · rfl
        · rfl
        · change Represents (recordLog result.payload ledger).ledger
            (ctx.plug (.node identity q (PoolTree.Tree.replaceChildren child.val.1
              result.next.erase (StoredTree.erasedChildren children))))
          rw [← hplugNext]
          exact ih.represents
      · change Allocated
          (ctx.plug (StoredRouting.delegatedNode identity q d children hp child.val child.property
            first second hf hs hr result.next).erase) result.counter
        rw [StoredRouting.erase_delegatedNode, PoolTree.Tree.delegatedNode]
        apply allocated_poolUpdate ctx identity q _ _ result.counter
        change Allocated (ctx.plug (.node identity q (PoolTree.Tree.replaceChildren child.val.1
          result.next.erase (StoredTree.erasedChildren children)))) result.counter
        rw [← hplugNext]
        exact ih.allocated
      · change Recorded (recordLog result.payload ledger).ledger.calls
          (StoredRouting.delegatedNode identity q d children hp child.val child.property
            first second hf hs hr result.next)
        rw [recordLog_calls]
        apply hrecorded.delegatedNode hp child.val child.property first second hf hs hr result.next
          [physicalRow result.payload]
        rw [← recordLog_calls]
        exact ih.recorded
termination_by sizeOf t
decreasing_by
  subst t
  exact hsize

end SortingAdversary.Optimal.LedgerRouter
