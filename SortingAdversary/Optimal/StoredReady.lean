import SortingAdversary.Optimal.PassiveLocalState
import SortingAdversary.Optimal.StoredRepair

/-!
# Preserving normalization throughout the stored tree

Only the stopping pool is repaired. All existing child pools retain their
normalization through independent admissions, and newborn children start with
an empty numerical graph. This holds for the exact child lists produced by
the concrete repair replay.
-/

namespace SortingAdversary.Optimal.StoredReady

open PoolState WeakMaps WeakMaps.WeakSystem WidthRepair GraphBalls
open PassiveLocalState StoredRouting
variable {n : ℕ}

theorem ready_empty_active (p : ScaleParameters) (D H : ℕ) (hD : 0 < D) (hH : 2 ≤ H)
    (q : Pool n) (d : LocalData q) (he : d.rows.active = fun _ _ => false) : Ready p D H q d := by
  have hn (x : Fin n) : neighbors d.rows.active x = ∅ := by simp [he, neighbors]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro x hx
    change (neighbors d.rows.active x).Nonempty at hx
    rw [hn x] at hx
    exact hx.elim (by simp)
  · intro x y hxy
    change d.rows.active x y = true at hxy
    rw [he] at hxy
    contradiction
  · intro x y hxy
    obtain ⟨r, hr⟩ := hxy
    change y ∈ ball d.rows.active x r at hr
    rw [IsolatedCoupling.ball_isolated d.rows.active x
      ((IsolatedCoupling.isolated_iff_neighbors_empty _ _).mpr (hn x)) r] at hr
    have hy := Finset.mem_singleton.mp hr
    subst y
    simpa using Nat.mul_le_mul_right ((state q d).width x) p.one_le_R
  · intro x
    rw [hn x, Finset.card_empty]
    exact hD
  · intro xs hx
    cases xs with
    | nil => simp; omega
    | cons x xs =>
      cases xs with
      | nil => simp; omega
      | cons y ys =>
        have hh := (List.isChain_cons_cons.mp hx).1.2
        rw [he] at hh
        contradiction

theorem empty_ready (p : ScaleParameters) (D H : ℕ) (hD : 0 < D) (hH : 2 ≤ H)
    (identity : ℕ) : AllNodes (Ready p D H) (StoredTree.empty n identity) := by
  rw [StoredTree.empty, allNodes_node]
  exact ⟨ready_empty_active p D H hD hH _ _ rfl, by simp⟩

theorem initial_ready (p : ScaleParameters) (D H : ℕ) (hD : 0 < D) (hH : 2 ≤ H)
    (N : ℕ) : AllNodes (Ready p D H) (StoredTree.initial N) := by
  rw [StoredTree.initial, allNodes_node]
  exact ⟨ready_empty_active p D H hD hH _ _ rfl, by simp⟩

theorem admitRoot_ready {p : ScaleParameters} {D H : ℕ} (t : StoredTree n)
    (h : AllNodes (Ready p D H) t) (v : Fin n) (hv : v ∉ t.pool.members) :
    AllNodes (Ready p D H) (t.admitRoot v hv) := by
  cases t with
  | node identity q d children =>
    obtain ⟨here, below⟩ := (allNodes_node _ _ _ _ _).mp h
    rw [StoredTree.admitRoot, allNodes_node]
    refine ⟨ready_admission q d here v hv, ?_⟩
    intro child hc
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hc
    exact below old ho

theorem freshChild_ready (p : ScaleParameters) (D H : ℕ) (hD : 0 < D) (hH : 2 ≤ H)
    (identity : ℕ) (v : Fin n) : AllNodes (Ready p D H) (StoredTree.freshChild n identity v) :=
  admitRoot_ready _ (empty_ready p D H hD hH identity) v _

theorem promotedChildren_ready {p : ScaleParameters} {D H : ℕ} {q : Pool n}
    {children : List (ℕ × StoredTree n)} (h : PoolTree.Tree.Parts q (StoredTree.erasedChildren children))
    (ready : ∀ a ∈ children, AllNodes (Ready p D H) a.2)
    (v : Fin n) (hv : q.pins v = none) (c : Fin (q.palette + 1))
    (r : Promotion.Result q.system q.pins v c) :
    ∀ a ∈ StoredTree.promotedChildren h v hv c r, AllNodes (Ready p D H) a.2 := by
  intro a ha
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ha
  dsimp only
  unfold StoredTree.promotedChild
  split
  · exact admitRoot_ready _ (ready old.val old.property) v _
  · exact ready old.val old.property

theorem replayStep_children_ready (p : ScaleParameters) (D H : ℕ) (hD : 0 < D) (hH : 2 ≤ H)
    (identity : ℕ) {s t : State n} (step : Step s t) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ready : ∀ a ∈ children, AllNodes (Ready p D H) a.2) :
    ∀ a ∈ (StoredRepair.replayStep identity step children hw ho counter).children,
      AllNodes (Ready p D H) a.2 := by
  cases step with
  | pin update =>
    have hh : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren children) := by
      apply PoolTree.Tree.parts
      simpa only [StoredRepair.erase_node] using hw
    change ∀ a ∈ (if PoolTree.Tree.destinationExists update.result (StoredTree.erasedChildren children) = true
      then StoredTree.promotedChildren hh update.vertex update.free update.colour update.result
      else StoredTree.promotedChildren hh update.vertex update.free update.colour update.result ++
        [(update.result.destination.val, StoredTree.freshChild n counter update.vertex)]), _
    split
    · exact promotedChildren_ready hh ready update.vertex update.free update.colour update.result
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact promotedChildren_ready hh ready update.vertex update.free update.colour update.result a ha
      · have he : a = (update.result.destination.val, StoredTree.freshChild n counter update.vertex) :=
          List.mem_singleton.mp ha
        subst a
        exact freshChild_ready p D H hD hH counter update.vertex
  | lowerCut => exact ready
  | upperCut => exact ready

theorem replayTrace_children_ready (p : ScaleParameters) (D H : ℕ) (hD : 0 < D) (hH : 2 ≤ H)
    (identity : ℕ) {s t : State n} (trace : Trace s t) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ready : ∀ a ∈ children, AllNodes (Ready p D H) a.2) :
    ∀ a ∈ (StoredRepair.replayTrace identity trace children hw ho counter).children,
      AllNodes (Ready p D H) a.2 := by
  induction trace generalizing children counter with
  | nil => exact ready
  | cons head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    exact ih first.children first.wellFormed first.coherent first.counter
      (replayStep_children_ready p D H hD hH identity head children hw ho counter ready)

end SortingAdversary.Optimal.StoredReady
