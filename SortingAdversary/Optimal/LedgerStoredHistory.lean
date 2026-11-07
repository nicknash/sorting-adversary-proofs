import SortingAdversary.Optimal.LedgerSourceHistory
import SortingAdversary.Optimal.StoredPromotion
import SortingAdversary.Optimal.StoredRouting

/-!
# Historical physical rows for the actual runtime tree

This recursive invariant covers the stored active matrices themselves.
Admissions retain their old rows, a parent promotion deletes incident rows,
and a new child starts without rows. Consequently a row witness survives the
actual parent/child mutation and the materialization used after each query.
-/

namespace SortingAdversary.Optimal.LedgerStoredHistory

open PoolState NumericalRepresentation LedgerSourceHistory IncidenceLedger

variable {n : ℕ}

inductive Recorded (calls : List (Option (Row n))) : StoredTree n → Prop
  | node (identity : ℕ) (p : Pool n) (d : LocalData p) (children : List (ℕ × StoredTree n))
      (here : RecordedRows calls identity d.rows.active)
      (below : ∀ a ∈ children, Recorded calls a.2) : Recorded calls (.node identity p d children)

theorem Recorded.here {calls : List (Option (Row n))} {identity : ℕ} {p : Pool n}
    {d : LocalData p} {children : List (ℕ × StoredTree n)}
    (h : Recorded calls (.node identity p d children)) : RecordedRows calls identity d.rows.active := by
  cases h
  assumption

theorem Recorded.children {calls : List (Option (Row n))} {identity : ℕ} {p : Pool n}
    {d : LocalData p} {children : List (ℕ × StoredTree n)}
    (h : Recorded calls (.node identity p d children)) (a : ℕ × StoredTree n) (ha : a ∈ children) :
    Recorded calls a.2 := by
  cases h with | node _ _ _ _ _ below => exact below a ha

theorem Recorded.append {calls : List (Option (Row n))} {t : StoredTree n}
    (h : Recorded calls t) (extra : List (Option (Row n))) : Recorded (calls ++ extra) t := by
  induction h with
  | node identity p d children here below ih =>
    exact .node identity p d children (here.append extra) (fun a ha => ih a ha)

theorem empty_recorded (calls : List (Option (Row n))) (identity : ℕ) :
    Recorded calls (StoredTree.empty n identity) := by
  refine .node _ _ _ _ ?_ (by simp)
  intro u v huv
  contradiction

theorem initial_recorded (N : ℕ) : Recorded [] (StoredTree.initial N) := by
  refine .node _ _ _ _ ?_ (by simp)
  intro u v huv
  contradiction

theorem mpr_active {p q : Pool n} (hp : p = q) (d : LocalData p)
    (he : LocalData q = LocalData p) : (he.mpr d).rows.active = d.rows.active := by
  cases hp
  rfl

theorem admission_active_old (p : Pool n) (d : LocalData p) (v : Fin n)
    (hv : v ∉ p.members) (x y : Fin n)
    (h : (d.admission p v hv).rows.active x y = true) : d.rows.active x y = true := by
  unfold LocalData.admission at h
  cases hd : ((p.members.card + 1).decLe (p.palette + 1)) with
  | isTrue hcap =>
    simp only [hd] at h
    have hp : p.admitSized v hv hcap = (p.admission v hv).next := by
      simp only [Pool.admission, dif_pos hcap]
    let data : LocalData (p.admitSized v hv hcap) :=
      ⟨d.rows.admit v (p.system.lower v) (p.outside v hv).2, d.order⟩
    have hh : ((congrArg LocalData hp.symm).mpr data).rows.active x y = true := h
    rw [mpr_active hp] at hh
    exact hh
  | isFalse hcap =>
    simp only [hd] at h
    have hp : p.append.admitSized v (by simpa only [Pool.append_members] using hv)
        (by exact Nat.succ_le_succ p.capacity) = (p.admission v hv).next := by
      simp only [Pool.admission, dif_neg hcap]
    let data : LocalData (p.append.admitSized v
        (by simpa only [Pool.append_members] using hv) (Nat.succ_le_succ p.capacity)) :=
      ⟨d.rows.append.admit v (p.append.system.lower v)
        (p.append.outside v (by simpa only [Pool.append_members] using hv)).2,
        PaletteBirthOrder.extendTop d.order⟩
    have hh : ((congrArg LocalData hp.symm).mpr data).rows.active x y = true := h
    rw [mpr_active hp] at hh
    exact (Bool.and_eq_true_iff.mp hh).1

theorem Recorded.admitRoot {calls : List (Option (Row n))} {t : StoredTree n}
    (h : Recorded calls t) (v : Fin n) (hv : v ∉ t.pool.members) :
    Recorded calls (t.admitRoot v hv) := by
  cases h with
  | node identity p d children here below =>
    rw [StoredTree.admitRoot]
    refine .node _ _ _ _ (here.mono (admission_active_old p d v hv)) ?_
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact below b hb

theorem freshChild_recorded (calls : List (Option (Row n))) (identity : ℕ) (v : Fin n) :
    Recorded calls (StoredTree.freshChild n identity v) :=
  (empty_recorded calls identity).admitRoot v _

theorem Recorded.promotedChild {calls : List (Option (Row n))} {p : Pool n}
    {children : List (ℕ × StoredTree n)}
    (h : PoolTree.Tree.Parts p (StoredTree.erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (a : ℕ × StoredTree n) (ha : a ∈ children)
    (recorded : Recorded calls a.2) :
    Recorded calls (StoredTree.promotedChild h v hv c r a ha) := by
  unfold StoredTree.promotedChild
  split
  · exact recorded.admitRoot v _
  · exact recorded

theorem Recorded.promotedNode {calls : List (Option (Row n))} {identity : ℕ} {p : Pool n}
    {d : LocalData p} {children : List (ℕ × StoredTree n)}
    (recorded : Recorded calls (.node identity p d children))
    (h : PoolTree.Tree.Parts p (StoredTree.erasedChildren children))
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c)
    (nextData : LocalData (p.installPromotion v hv c r))
    (activeOld : ∀ x y, nextData.rows.active x y = true → d.rows.active x y = true)
    (nextIdentity : ℕ) :
    Recorded calls (StoredTree.promotedNode identity p children h v hv c r nextData nextIdentity) := by
  have hbelow : ∀ a ∈ StoredTree.promotedChildren h v hv c r, Recorded calls a.2 := by
    intro a ha
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp ha
    exact Recorded.promotedChild h v hv c r b hb (recorded.children b hb)
  dsimp only [StoredTree.promotedNode]
  split
  · exact .node _ _ _ _ (recorded.here.mono activeOld) hbelow
  · refine .node _ _ _ _ (recorded.here.mono activeOld) ?_
    intro a ha
    rcases List.mem_append.mp ha with hold | hnew
    · exact hbelow a hold
    · obtain rfl := List.mem_singleton.mp hnew
      exact freshChild_recorded calls nextIdentity v

theorem Recorded.poolUpdate {calls : List (Option (Row n))} {identity : ℕ} {p : Pool n}
    {d : LocalData p} {children : List (ℕ × StoredTree n)}
    (recorded : Recorded calls (.node identity p d children)) (q : Pool n) (nextData : LocalData q)
    (activeOld : ∀ x y, nextData.rows.active x y = true → d.rows.active x y = true) :
    Recorded calls (.node identity q nextData children) :=
  .node _ _ _ _ (recorded.here.mono activeOld) recorded.children

theorem Recorded.materialize {calls : List (Option (Row n))} {t : StoredTree n}
    (h : Recorded calls t) : Recorded calls t.materialize := by
  induction h with
  | node identity p d children here below ih =>
    rw [StoredTree.materialize]
    refine .node _ _ _ _ ?_ ?_
    · rw [mpr_active (Materialize.pool_eq p).symm]
      simpa only [LocalData.materialize_eq] using here
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb

theorem Recorded.stopNode {calls : List (Option (Row n))} {identity : ℕ} {p : Pool n}
    {d : LocalData p} {children : List (ℕ × StoredTree n)}
    (recorded : Recorded calls (.node identity p d children))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members) (hab : a ≠ b)
    (hi : ControllerRouting.Invariant (Safety.closedAdd p.system a b) p.pins) :
    Recorded (calls ++ [callRow identity p a b])
      (StoredRouting.stopNode identity p d children a b ha hb hab hi) :=
  .node _ _ _ _ (recorded.here.add p d.rows a b hab)
    (fun child hc => (recorded.children child hc).append _)

/-- An ancestor stores its public comparison, but its endpoints are physical
pins. The only new chronological row is the one recorded at the stopping node. -/
theorem Recorded.delegatedNode {calls : List (Option (Row n))} {identity : ℕ} {p : Pool n}
    {d : LocalData p} {children : List (ℕ × StoredTree n)}
    (recorded : Recorded calls (.node identity p d children))
    (h : PoolTree.Tree.Parts p (StoredTree.erasedChildren children))
    (target : ℕ × StoredTree n) (ht : target ∈ children)
    (a b : Fin n) (ha : a ∈ target.2.pool.members) (hb : b ∈ target.2.pool.members)
    (hba : p.system.edge b a ≠ true) (next : StoredTree n)
    (extra : List (Option (Row n))) (hn : Recorded (calls ++ extra) next) :
    Recorded (calls ++ extra)
      (StoredRouting.delegatedNode identity p d children h target ht a b ha hb hba next) := by
  have hpin : p.pins a ≠ none := by
    obtain ⟨c, hc, _⟩ := h.pin_witness (StoredRouting.semanticChild target)
      (StoredRouting.semanticChild_mem ht) a (by simpa only [StoredRouting.semanticChild_pool] using ha)
    rw [hc]
    exact Option.some_ne_none c
  dsimp only [StoredRouting.delegatedNode]
  refine .node _ _ _ _ ?_ ?_
  · change RecordedRows (calls ++ extra) identity
      (d.rows.add a b (StoredRouting.distinct_of_reverse_unknown p a b hba)).active
    rw [SourcePartition.add_active_pinned_left _ _ _ _ hpin]
    exact recorded.here.append extra
  · intro child hc
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hc
    by_cases hk : old.1 = target.1
    · simpa only [if_pos hk] using hn
    · simpa only [if_neg hk] using (recorded.children old hold).append extra

end SortingAdversary.Optimal.LedgerStoredHistory
