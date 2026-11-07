import SortingAdversary.Optimal.StoredPromotion
import SortingAdversary.Optimal.TreeRootChange
import SortingAdversary.Optimal.WidthRepair

/-!
# Replay a concrete local repair execution into the stored child tree

Every parent pin performs its actual destination admission, including a new
child when needed. Its rational loss is divided by the exact birthday
multiplier. Strict cuts keep all children and their numerical laws unchanged.
The finite replay retains primitive numerical data, palette identities, and
the complete public-order and counting certificates.
-/

namespace SortingAdversary.Optimal.StoredRepair

open PoolState WeakMaps WeakMaps.WeakSystem WidthRepair
open PoolTree.Tree PoolPalette TreeChronology
variable {n : ℕ}

def node (identity : ℕ) (s : State n) (children : List (ℕ × StoredTree n)) : StoredTree n :=
  .node identity s.pool ⟨s.rows, s.order⟩ children

@[simp] theorem erase_node (identity : ℕ) (s : State n) (children : List (ℕ × StoredTree n)) :
    (node identity s children).erase = PoolTree.Tree.node identity s.pool (StoredTree.erasedChildren children) := by
  rw [node, StoredTree.erase]
  rfl

theorem promotion_ratio_retention
    (identity : ℕ) (p : Pool n) (children : List (ℕ × PoolTree.Tree n))
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (freshIdentity : ℕ) (charge : ℚ) (hr : (p.system.count : ℚ) ≤ charge * r.system.count) :
    ((PoolTree.Tree.node identity p children).count : ℚ) ≤
      (charge / birthMultiplier h v hv c r) *
        (promotedNode identity p children h v hv c r freshIdentity).count := by
  have hb : (birthMultiplier h v hv c r : ℚ) ≠ 0 := by
    exact_mod_cast (birthMultiplier_pos h v hv c r).ne'
  rw [PoolTree.Tree.count, promotedNode_count]
  simp only [Nat.cast_mul]
  let childrenCount : ℕ := (children.map (fun a => a.2.count)).prod
  change (p.system.count : ℚ) * childrenCount ≤
    (charge / birthMultiplier h v hv c r) *
      ((r.system.count : ℚ) * childrenCount * birthMultiplier h v hv c r)
  calc
    (p.system.count : ℚ) * childrenCount ≤
        (charge * r.system.count) * childrenCount :=
      mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
    _ = (charge / birthMultiplier h v hv c r) *
        ((r.system.count : ℚ) * childrenCount *
          birthMultiplier h v hv c r) := by field_simp

structure Result (identity : ℕ) (before : State n) (oldChildren : List (ℕ × StoredTree n))
    (after : State n) where
  children : List (ℕ × StoredTree n)
  counter : ℕ
  charge : ℚ
  wellFormed : (node identity after children).erase.WellFormed
  coherent : (node identity after children).erase.Coherent
  bounded : TreeBounded (node identity before oldChildren).erase →
    TreeBounded (node identity after children).erase
  retention : ((node identity before oldChildren).erase.count : ℚ) ≤
    charge * (node identity after children).erase.count

theorem Result.charge_pos {identity : ℕ} {s t : State n}
    {children : List (ℕ × StoredTree n)} (r : Result identity s children t) : 0 < r.charge := by
  have hs : (0 : ℚ) < (node identity s children).erase.count := by
    exact_mod_cast (node identity s children).erase.count_pos
  have ht : (0 : ℚ) < (node identity t r.children).erase.count := by
    exact_mod_cast (node identity t r.children).erase.count_pos
  exact pos_of_mul_pos_left (hs.trans_le r.retention) ht.le

def replayStep (identity : ℕ) {s t : State n} (step : Step s t)
    (children : List (ℕ × StoredTree n))
    (hw : (node identity s children).erase.WellFormed)
    (ho : (node identity s children).erase.Coherent) (counter : ℕ) :
    Result identity s children t := by
  rw [erase_node] at hw ho
  let h := parts hw
  cases step with
  | pin update =>
    let old := StoredTree.promotedChildren h update.vertex update.free update.colour update.result
    let nextChildren := if destinationExists update.result (StoredTree.erasedChildren children) = true then old
      else old ++ [(update.result.destination.val, StoredTree.freshChild n counter update.vertex)]
    let data : LocalData (s.pool.installPromotion update.vertex update.free update.colour update.result) :=
      ⟨update.data.rows, update.data.order⟩
    have hshape : node identity update.next nextChildren =
        StoredTree.promotedNode identity s.pool children h update.vertex update.free update.colour
          update.result data counter := by
      by_cases he : destinationExists update.result (StoredTree.erasedChildren children) = true
      · simp only [node, nextChildren, old, StoredTree.promotedNode, if_pos he]
        rfl
      · simp only [node, nextChildren, old, StoredTree.promotedNode, if_neg he]
        rfl
    have herase : (node identity update.next nextChildren).erase =
        promotedNode identity s.pool (StoredTree.erasedChildren children) h
          update.vertex update.free update.colour update.result counter :=
      (congrArg StoredTree.erase hshape).trans (StoredTree.erase_promotedNode _ _ _ _ _ _ _ _ _ _)
    refine {
      children := nextChildren
      counter := nextIdentityAfter update.result (StoredTree.erasedChildren children) counter
      charge := update.charge / birthMultiplier h update.vertex update.free update.colour update.result
      wellFormed := ?_
      coherent := ?_
      bounded := ?_
      retention := ?_ }
    · rw [herase]
      exact promotedNode_wellFormed identity s.pool _ h update.vertex update.free update.colour
        update.result update.mate counter
    · rw [herase]
      exact promotedNode_coherent identity s.pool _ h ho update.vertex update.free update.colour
        update.result counter
    · intro hb
      rw [erase_node] at hb
      rw [herase]
      exact promotedNode_bounded identity s.pool _ h update.vertex update.free update.colour
        update.result counter hb
    · rw [erase_node, herase]
      exact promotion_ratio_retention identity s.pool _ h update.vertex update.free update.colour
        update.result counter update.charge update.retained
  | lowerCut u v live ratio charge retained =>
    refine {
      children := children
      counter := counter
      charge := charge
      wellFormed := ?_
      coherent := ?_
      bounded := ?_
      retention := ?_ }
    · rw [erase_node]
      exact (parts_change_root h (s.lowerCut u v live ratio).pool rfl rfl (fun _ => rfl)
        (s.lowerCut_separated u v live ratio h.separated)).wellFormed identity
    · rw [erase_node]
      exact coherent_change_root identity s.pool _ _ ho rfl
    · intro hb
      rw [erase_node] at hb ⊢
      exact bounded_change_root identity s.pool _ _ hb rfl rfl (fun _ => rfl)
    · rw [erase_node, erase_node]
      exact root_change_retention identity s.pool _ _ charge retained
  | upperCut u v live ratio charge retained =>
    refine {
      children := children
      counter := counter
      charge := charge
      wellFormed := ?_
      coherent := ?_
      bounded := ?_
      retention := ?_ }
    · rw [erase_node]
      exact (parts_change_root h (s.upperCut u v live ratio).pool rfl rfl (fun _ => rfl)
        (s.upperCut_separated u v live ratio h.separated)).wellFormed identity
    · rw [erase_node]
      exact coherent_change_root identity s.pool _ _ ho rfl
    · intro hb
      rw [erase_node] at hb ⊢
      exact bounded_change_root identity s.pool _ _ hb rfl rfl (fun _ => rfl)
    · rw [erase_node, erase_node]
      exact root_change_retention identity s.pool _ _ charge retained

/-- Replay the exact chronological parent execution. No extra promotion,
child repair, or interval change is introduced by this tree layer. -/
def replayTrace (identity : ℕ) {s t : State n} (trace : Trace s t)
    (children : List (ℕ × StoredTree n))
    (hw : (node identity s children).erase.WellFormed)
    (ho : (node identity s children).erase.Coherent) (counter : ℕ) :
    Result identity s children t :=
  match trace with
  | .nil _ => ⟨children, counter, 1, hw, ho, id, by simp⟩
  | .cons head tail =>
    let first := replayStep identity head children hw ho counter
    let rest := replayTrace identity tail first.children first.wellFormed first.coherent first.counter
    { children := rest.children
      counter := rest.counter
      charge := first.charge * rest.charge
      wellFormed := rest.wellFormed
      coherent := rest.coherent
      bounded := fun hb => rest.bounded (first.bounded hb)
      retention := first.retention.trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left rest.retention first.charge_pos.le) }

end SortingAdversary.Optimal.StoredRepair
