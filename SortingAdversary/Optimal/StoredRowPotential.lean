import SortingAdversary.Optimal.LedgerStoredReplay
import SortingAdversary.Optimal.NormalizedBounds

/-!
# The actual stored active-row potential

An admission adds an isolated child member. Thus a parent repair changes
the active-row potential only at that parent; its real descendant updates
preserve their contribution. A delegated comparison also preserves the
ancestor's active rows. These exact identities let the whole-run cut bound
charge each retired row to one physical stopping insertion.
-/

namespace SortingAdversary.Optimal.StoredRowPotential

open PoolState WidthRepair SparseRepairGraph PoolTree.Tree StoredRouting

variable {n : ℕ}

def rows (tree : StoredTree n) : ℕ :=
  match tree with
  | .node _ _ d children => (rawRows d.rows.active).card + (children.map (fun a => rows a.2)).sum
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹a ∈ children›
  cases a
  simp_wf
  simp only [Prod.mk.sizeOf_spec] at h
  omega

theorem rows_admitRoot (tree : StoredTree n) (v : Fin n) (hv : v ∉ tree.pool.members) :
    rows (tree.admitRoot v hv) = rows tree := by
  cases tree with
  | node identity p d children =>
    change v ∉ p.members at hv
    change rows (.node identity (p.admission v hv).next (d.admission p v hv)
      (StoredTree.mapKeys (p.admission v hv).embed children)) = rows (.node identity p d children)
    rw [rows, rows, PassiveLocalState.admission_active p d v hv]
    simp only [StoredTree.mapKeys, List.map_map, Function.comp_def]

@[simp] theorem rows_empty (n identity : ℕ) : rows (StoredTree.empty n identity) = 0 := by
  simp [StoredTree.empty, rows, emptyData, rawRows]

@[simp] theorem rows_initial (N : ℕ) : rows (StoredTree.initial N) = 0 := by
  simp [StoredTree.initial, rows, initialData, rawRows]

@[simp] theorem rows_freshChild (n identity : ℕ) (v : Fin n) :
    rows (StoredTree.freshChild n identity v) = 0 := by
  rw [StoredTree.freshChild, rows_admitRoot, rows_empty]

theorem rows_promotedChild {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : Parts p (StoredTree.erasedChildren children)) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (a : ℕ × StoredTree n) (ha : a ∈ children) :
    rows (StoredTree.promotedChild h v hv c r a ha) = rows a.2 := by
  unfold StoredTree.promotedChild
  split
  · exact rows_admitRoot _ _ _
  · rfl

theorem rows_promotedChildren {p : Pool n} {children : List (ℕ × StoredTree n)}
    (h : Parts p (StoredTree.erasedChildren children)) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    ((StoredTree.promotedChildren h v hv c r).map (fun a => rows a.2)).sum =
      (children.map (fun a => rows a.2)).sum := by
  simp only [StoredTree.promotedChildren, List.map_map, Function.comp_def, rows_promotedChild]
  exact congrArg List.sum (List.attach_map_val (l := children) (f := fun a : ℕ × StoredTree n => rows a.2))

theorem rows_promotedNode (identity : ℕ) (p : Pool n) (children : List (ℕ × StoredTree n))
    (h : Parts p (StoredTree.erasedChildren children)) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (d : LocalData (p.installPromotion v hv c r)) (fresh : ℕ) :
    rows (StoredTree.promotedNode identity p children h v hv c r d fresh) =
      (rawRows d.rows.active).card + (children.map (fun a => rows a.2)).sum := by
  unfold StoredTree.promotedNode
  dsimp only
  split <;> simp only [rows, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, rows_freshChild, Nat.add_zero,
    rows_promotedChildren]

theorem replayStep_children (identity : ℕ) {s t : State n} (step : Step s t)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    ((StoredRepair.replayStep identity step children hw ho counter).children.map (fun a => rows a.2)).sum =
      (children.map (fun a => rows a.2)).sum := by
  cases step with
  | pin update =>
    have hp := parts (by simpa only [StoredRepair.erase_node] using hw)
    have he := congrArg rows (LedgerStoredReplay.replayStep_pin_shape identity update children hw ho counter hp)
    rw [rows_promotedNode] at he
    rw [StoredRepair.node, rows] at he
    change (rawRows update.next.rows.active).card + _ = _ at he
    exact Nat.add_left_cancel he
  | lowerCut => rfl
  | upperCut => rfl

theorem replayTrace_children (identity : ℕ) {s t : State n} (trace : Trace s t)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    ((StoredRepair.replayTrace identity trace children hw ho counter).children.map (fun a => rows a.2)).sum =
      (children.map (fun a => rows a.2)).sum := by
  induction trace generalizing children counter with
  | nil => rfl
  | cons head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    exact (ih first.children first.wellFormed first.coherent first.counter).trans
      (replayStep_children identity head children hw ho counter)

theorem added_rows_le (p : Pool n) (d : LocalData p) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hne : a ≠ b)
    (hi : ControllerRouting.Invariant (Safety.closedAdd p.system a b) p.pins) :
    (rawRows (d.add p a b ha hb hne hi).rows.active).card ≤ (rawRows d.rows.active).card + 1 := by
  have hsub : rawRows (d.add p a b ha hb hne hi).rows.active ⊆ insert (a, b) (rawRows d.rows.active) := by
    intro z hz
    have h := NormalizedBounds.added_active_subset p d a b ha hb hne hi z.1 z.2
      ((mem_rawRows _ _ _).mp hz).2
    rcases (addRow_true _ _ _ _ _).mp h with hold | hnew
    · exact Finset.mem_insert_of_mem ((mem_rawRows _ _ _).mpr ⟨((mem_rawRows _ _ _).mp hz).1, hold⟩)
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hnew.1 hnew.2))
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem rows_stopNode (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (a b : Fin n)
    (ha : a ∈ p.members) (hb : b ∈ p.members) (hne : a ≠ b)
    (hi : ControllerRouting.Invariant (Safety.closedAdd p.system a b) p.pins) :
    rows (stopNode identity p d children a b ha hb hne hi) ≤
      rows (.node identity p d children) + 1 := by
  have h := added_rows_le p d a b ha hb hne hi
  simp only [StoredRouting.stopNode, rows]
  omega

theorem replace_children_rows (children : List (ℕ × StoredTree n))
    (hk : (children.map Prod.fst).Nodup) (target : ℕ × StoredTree n) (ht : target ∈ children)
    (next : StoredTree n) :
    ((replaceChildren target.1 next children).map (fun a => rows a.2)).sum + rows target.2 =
      (children.map (fun a => rows a.2)).sum + rows next := by
  induction children with
  | nil => simp at ht
  | cons head rest ih =>
    have hn := List.nodup_cons.mp hk
    rcases List.mem_cons.mp ht with he | ht
    · subst head
      have hrest : replaceChildren target.1 next rest = rest := by
        unfold StoredRouting.replaceChildren
        conv_rhs => rw [← List.map_id rest]
        apply List.map_congr_left
        intro a ha
        have hne : a.1 ≠ target.1 := by
          intro heq
          exact hn.1 (heq ▸ List.mem_map.mpr ⟨a, ha, rfl⟩)
        simp [hne]
      simp only [StoredRouting.replaceChildren, List.map_cons, ite_true, List.sum_cons]
      change _ + (((replaceChildren target.1 next rest).map (fun a => rows a.2)).sum) + _ = _
      rw [hrest]
      omega
    · have hne : head.1 ≠ target.1 := by
        intro heq
        exact hn.1 (heq.symm ▸ List.mem_map.mpr ⟨target, ht, rfl⟩)
      have h := ih hn.2 ht
      simp only [StoredRouting.replaceChildren, List.map_cons, if_neg hne, List.sum_cons] at h ⊢
      omega

theorem rows_delegatedNode (identity : ℕ) (p : Pool n) (d : LocalData p)
    (children : List (ℕ × StoredTree n)) (h : Parts p (StoredTree.erasedChildren children))
    (target : ℕ × StoredTree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : StoredTree n) :
    rows (delegatedNode identity p d children h target ht a b ha hb hba next) + rows target.2 =
      rows (.node identity p d children) + rows next := by
  have hk : (children.map Prod.fst).Nodup := by
    simpa only [StoredTree.erasedChildren, List.map_map, Function.comp_def] using h.keys
  have hpin : p.pins a ≠ none := by
    have hm := (h.members (semanticChild target) (semanticChild_mem ht) a).mp
      (by simpa only [semanticChild, StoredTree.erase_pool] using ha)
    intro hnone
    simp [pinIndex, hnone] at hm
  have hactive := d.rows.add_active_pinned_left a b (distinct_of_reverse_unknown p a b hba) hpin
  have hs := replace_children_rows children hk target ht next
  unfold StoredRouting.delegatedNode
  simp only [rows, LocalData.add, hactive]
  omega

end SortingAdversary.Optimal.StoredRowPotential
