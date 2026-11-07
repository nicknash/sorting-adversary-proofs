import SortingAdversary.Optimal.RepresentationTreeView

/-!
# Counted replay of the executable tree projections

Only the next physical node, its cached getter records, and the allocator
counter are computed. Birthday multipliers, rational charges, and accounting
payloads stay in erased proofs. Recursive replay rebases the remaining trace
onto each physically stored state before continuing.
-/

namespace SortingAdversary.Optimal.RepresentationWork

open PrimitiveWork WidthRepair PoolState PoolPalette
variable {n : ℕ} {s t : State n}

def ReplayOutput.changeCounter {s : State n} {children : List (ℕ × StoredTree n)}
    {k l : ℕ} (eq : k = l) (out : ReplayOutput s children k) : ReplayOutput s children l := eq ▸ out

namespace TreeReplay

def step (identity : ℕ) (a : LocalAccess s) {children : List (ℕ × StoredTree n)}
    (ch : ChildrenAccess children) (ha : AccessBound a 2) (hch : ch.Bound 2)
    (transition : Step s t) (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    Result (ReplayOutput t (StoredRepair.replayStep identity transition children hw ho counter).children
      (StoredRepair.replayStep identity transition children hw ho counter).counter) := by
  have parts : PoolTree.Tree.Parts s.pool (StoredTree.erasedChildren children) :=
    PoolTree.Tree.parts (by simpa only [StoredRepair.erase_node] using hw)
  cases transition with
  | pin update =>
    let next := a.step (.pin update)
    let keys := a.pinKeys update
    let data : LocalData (s.pool.installPromotion update.vertex update.free update.colour update.result) :=
      ⟨update.data.rows, update.data.order⟩
    let node := TreeAccess.promotedNode identity ch parts update.vertex update.free update.colour
      update.result data next.value keys.value counter
    have he : StoredTree.promotedNode identity s.pool children parts update.vertex update.free update.colour
        update.result data counter = StoredRepair.node identity update.next
          (StoredRepair.replayStep identity (.pin update) children hw ho counter).children := by
      unfold StoredTree.promotedNode StoredRepair.replayStep
      dsimp only
      split <;> rfl
    have hbound := TreeAccess.promotedNode_bound identity ch parts update.vertex update.free update.colour
      update.result data next.value keys.value counter (LocalAccess.step_access a (.pin update)) hch
    let out := ReplayOutput.ofTree (node.value.1.transport he) (TreeAccess.transport_bound _ _ hbound) node.value.2
    have hc : node.value.2 = (StoredRepair.replayStep identity (.pin update) children hw ho counter).counter :=
      TreeAccess.promotedNode_counter identity ch parts update.vertex update.free update.colour
        update.result data next.value keys.value counter
    exact ⟨out.changeCounter hc, next.work + keys.work + node.work + 20⟩
  | lowerCut u v live ratio charge retained =>
    let transition := Step.lowerCut s u v live ratio charge retained
    let next := a.step transition
    let node := TreeAccess.pack identity next.value s.pool.palette s.pool.members rfl rfl ch
    exact ⟨ReplayOutput.ofTree node.value
      (TreeAccess.pack_bound _ _ _ _ _ _ _ (LocalAccess.step_access a transition) hch) counter,
      next.work + node.work + 20⟩
  | upperCut u v live ratio charge retained =>
    let transition := Step.upperCut s u v live ratio charge retained
    let next := a.step transition
    let node := TreeAccess.pack identity next.value s.pool.palette s.pool.members rfl rfl ch
    exact ⟨ReplayOutput.ofTree node.value
      (TreeAccess.pack_bound _ _ _ _ _ _ _ (LocalAccess.step_access a transition) hch) counter,
      next.work + node.work + 20⟩

def stepBound (n : ℕ) : ℕ :=
  LocalAccess.updateBound n (treeShapeBound n) 2 +
    2 * WindowWork.endpointWorkBound n 2 2 + 8 +
    TreeAccess.promotionBound n 7 (treeShapeBound n) (treeShapeBound n) (treeShapeBound n) + 60

theorem step_work (identity : ℕ) (a : LocalAccess s) {children : List (ℕ × StoredTree n)}
    (ch : ChildrenAccess children) (ha : AccessBound a 2) (hch : ch.Bound 2)
    (transition : Step s t) (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (hb : TreeBounded (StoredRepair.node identity s children).erase) :
    (step identity a ch ha hch transition hw ho counter).work ≤ stepBound n := by
  have hroot := stored_palette_size (StoredRepair.node identity s children) hb
  have hpal : s.pool.palette ≤ treeShapeBound n := by
    change s.pool.palette + 1 ≤ treeShapeBound n at hroot
    omega
  have hlen : children.length ≤ treeShapeBound n :=
    stored_children_length (StoredRepair.node identity s children) hw hb
  have hchildren := node_child_bounds identity s hw hb
  have hupdate := (LocalAccess.step_work_le a ha transition).trans (LocalAccess.updateBound_mono hpal)
  cases transition with
  | pin update =>
    have hkeys := LocalAccess.pinKeys_work a ha update
    have hnode := TreeAccess.promotedNode_work identity ch
      (PoolTree.Tree.parts (by simpa only [StoredRepair.erase_node] using hw))
      update.vertex update.free update.colour update.result ⟨update.data.rows, update.data.order⟩
      (a.step (.pin update)).value (a.pinKeys update).value counter hch (LocalAccess.pinKeys_bound a update)
      hchildren.1 hchildren.2
    have hsize : TreeAccess.promotionBound n 7 (treeShapeBound n) (treeShapeBound n) children.length ≤
        TreeAccess.promotionBound n 7 (treeShapeBound n) (treeShapeBound n) (treeShapeBound n) := by
      unfold TreeAccess.promotionBound
      gcongr
    change _ + _ + _ + 20 ≤ _
    unfold stepBound
    omega
  | lowerCut u v live ratio charge retained =>
    change _ + 40 + 20 ≤ _
    unfold stepBound
    omega
  | upperCut u v live ratio charge retained =>
    change _ + 40 + 20 ≤ _
    unfold stepBound
    omega

def fromState {s t u : State n} (he : u = s) (trace : Trace s t) : Trace u t := he.symm ▸ trace

@[simp] theorem fromState_length {s t u : State n} (he : u = s) (trace : Trace s t) :
    (fromState he trace).length = trace.length := by cases he; rfl

theorem reference_transport (identity : ℕ) {s t u : State n} (trace : Trace s t)
    (he : u = s) {children nextChildren : List (ℕ × StoredTree n)}
    (hc : nextChildren = children) {counter nextCounter : ℕ} (hk : nextCounter = counter)
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent)
    (hw' : (StoredRepair.node identity u nextChildren).erase.WellFormed)
    (ho' : (StoredRepair.node identity u nextChildren).erase.Coherent) :
    (StoredRepair.replayTrace identity (fromState he trace) nextChildren hw' ho' nextCounter).children =
        (StoredRepair.replayTrace identity trace children hw ho counter).children ∧
      (StoredRepair.replayTrace identity (fromState he trace) nextChildren hw' ho' nextCounter).counter =
        (StoredRepair.replayTrace identity trace children hw ho counter).counter := by
  cases he
  cases hc
  cases hk
  exact ⟨rfl, rfl⟩

def run (identity : ℕ) {s t : State n} (trace : Trace s t) (a : LocalAccess s)
    {children : List (ℕ × StoredTree n)} (ch : ChildrenAccess children)
    (ha : AccessBound a 2) (hch : ch.Bound 2)
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    Result (ReplayOutput t (StoredRepair.replayTrace identity trace children hw ho counter).children
      (StoredRepair.replayTrace identity trace children hw ho counter).counter) :=
  match trace with
  | .nil _ =>
    let node := TreeAccess.pack identity a s.pool.palette s.pool.members rfl rfl ch
    ⟨ReplayOutput.ofTree node.value (TreeAccess.pack_bound _ _ _ _ _ _ _ ha hch) counter,
      node.work + 20⟩
  | .cons head tail =>
    let first := step identity a ch ha hch head hw ho counter
    let reference := StoredRepair.replayStep identity head children hw ho counter
    have hw' : (StoredRepair.node identity first.value.state first.value.nextChildren).erase.WellFormed := by
      rw [first.value.state_eq, first.value.children_eq]
      exact reference.wellFormed
    have ho' : (StoredRepair.node identity first.value.state first.value.nextChildren).erase.Coherent := by
      rw [first.value.state_eq, first.value.children_eq]
      exact reference.coherent
    let rest := run identity (fromState first.value.state_eq tail) first.value.access first.value.nextAccess
      first.value.cached first.value.children_cached hw' ho' first.value.nextCounter
    have consistent := reference_transport identity tail first.value.state_eq first.value.children_eq
      first.value.counter_eq reference.wellFormed reference.coherent hw' ho'
    ⟨{
      state := rest.value.state
      nextChildren := rest.value.nextChildren
      access := rest.value.access
      nextAccess := rest.value.nextAccess
      nextCounter := rest.value.nextCounter
      state_eq := rest.value.state_eq
      children_eq := rest.value.children_eq.trans consistent.1
      counter_eq := rest.value.counter_eq.trans consistent.2
      cached := rest.value.cached
      children_cached := rest.value.children_cached }, first.work + rest.work + 20⟩
termination_by trace.length
decreasing_by simp only [fromState_length, Trace.length]; omega

theorem run_work (identity : ℕ) {s t : State n} (trace : Trace s t) (a : LocalAccess s)
    {children : List (ℕ × StoredTree n)} (ch : ChildrenAccess children)
    (ha : AccessBound a 2) (hch : ch.Bound 2)
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (hb : TreeBounded (StoredRepair.node identity s children).erase) :
    (run identity trace a ch ha hch hw ho counter).work ≤ trace.length * (stepBound n + 20) + 60 := by
  cases htrace : trace with
  | nil => simp only [run, TreeAccess.pack_work, Trace.length, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons head tail =>
    let first := step identity a ch ha hch head hw ho counter
    let reference := StoredRepair.replayStep identity head children hw ho counter
    have hw' : (StoredRepair.node identity first.value.state first.value.nextChildren).erase.WellFormed := by
      rw [first.value.state_eq, first.value.children_eq]
      exact reference.wellFormed
    have ho' : (StoredRepair.node identity first.value.state first.value.nextChildren).erase.Coherent := by
      rw [first.value.state_eq, first.value.children_eq]
      exact reference.coherent
    have hb' : TreeBounded (StoredRepair.node identity first.value.state first.value.nextChildren).erase := by
      rw [first.value.state_eq, first.value.children_eq]
      exact reference.bounded hb
    have hf := step_work identity a ch ha hch head hw ho counter hb
    have hr := run_work identity (fromState first.value.state_eq tail) first.value.access first.value.nextAccess
      first.value.cached first.value.children_cached hw' ho' first.value.nextCounter hb'
    rw [fromState_length] at hr
    rw [run]
    change first.work + _ + 20 ≤ _
    dsimp only [first] at hr ⊢
    simp only [Trace.length, Nat.add_mul, one_mul]
    omega
termination_by trace.length
decreasing_by
  rw [fromState_length, htrace]
  simp only [Trace.length]
  omega

end TreeReplay

end SortingAdversary.Optimal.RepresentationWork
