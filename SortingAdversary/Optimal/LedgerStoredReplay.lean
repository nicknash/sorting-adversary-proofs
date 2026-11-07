import SortingAdversary.Optimal.LedgerStoredHistory
import SortingAdversary.Optimal.LedgerReplayLabels
import SortingAdversary.Optimal.StoredRepair

/-!
# The actual stored repair emits an accepted chronological ledger

The action list follows `StoredRepair.replayStep` and `replayTrace`, including
their computed receiving child and allocator counter. Source witnesses come
from the repair's initial active graph. The classifier is computed from the
normalizer's event annotations in `LedgerReplayLabels`.
-/

namespace SortingAdversary.Optimal.LedgerStoredReplay

open PoolState WidthRepair PoolTree.Tree TreeChronology LedgerTreeBridge
open LedgerTreeTransitions LedgerSourceHistory LedgerStoredHistory LedgerReplayLabels
open IncidenceLedger (Kind Action Row)

variable {n : ℕ}

def stepActions (identity : ℕ) {s t : State n} (step : Step s t) (label : StepLabel step)
    (children : List (ℕ × StoredTree n)) (counter : ℕ) : List (Action n) :=
  match step, label with
  | .pin update, kind =>
      promotionActions identity update.vertex kind update.result (StoredTree.erasedChildren children) counter
  | .lowerCut .., _ => []
  | .upperCut .., _ => []

def stepLedger (identity : ℕ) {s t : State n} (step : Step s t) (label : StepLabel step)
    (children : List (ℕ × StoredTree n)) (counter : ℕ)
    (ledger : IncidenceLedger.State n) : IncidenceLedger.State n :=
  match step, label with
  | .pin update, kind =>
      promotionLedger ledger identity update.vertex kind update.result (StoredTree.erasedChildren children) counter
  | .lowerCut .., _ => ledger
  | .upperCut .., _ => ledger

theorem replayStep_pin_shape (identity : ℕ) {s : State n} (update : PinUpdate s)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (h : Parts s.pool (StoredTree.erasedChildren children)) :
    StoredRepair.node identity update.next
      (StoredRepair.replayStep identity (.pin update) children hw ho counter).children =
      StoredTree.promotedNode identity s.pool children h update.vertex update.free update.colour
        update.result ⟨update.data.rows, update.data.order⟩ counter := by
  by_cases hex : destinationExists update.result (StoredTree.erasedChildren children) = true
  · simp only [StoredRepair.replayStep, StoredRepair.node, StoredTree.promotedNode, if_pos hex]
    rfl
  · simp only [StoredRepair.replayStep, StoredRepair.node, StoredTree.promotedNode, if_neg hex]
    rfl

theorem replayStep_pin_counter (identity : ℕ) {s : State n} (update : PinUpdate s)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    (StoredRepair.replayStep identity (.pin update) children hw ho counter).counter =
      nextIdentityAfter update.result (StoredTree.erasedChildren children) counter := rfl

theorem allocated_poolUpdate (ctx : Context n) (identity : ℕ) (p q : Pool n)
    (children : List (ℕ × PoolTree.Tree n)) (counter : ℕ)
    (ha : Allocated (ctx.plug (.node identity p children)) counter) :
    Allocated (ctx.plug (.node identity q children)) counter := by
  apply allocated_of_perm ha
  rw [Context.plug_identities, Context.plug_identities, identities_node, identities_node]

theorem replayStep_allocated (ctx : Context n) (identity : ℕ) {s t : State n} (step : Step s t)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter) :
    Allocated (ctx.plug (StoredRepair.node identity t
      (StoredRepair.replayStep identity step children hw ho counter).children).erase)
      (StoredRepair.replayStep identity step children hw ho counter).counter := by
  cases step with
  | pin update =>
    let h : Parts s.pool (StoredTree.erasedChildren children) := parts (by simpa using hw)
    rw [replayStep_pin_shape identity update children hw ho counter h,
      StoredTree.erase_promotedNode, replayStep_pin_counter]
    exact ctx.promotedNode_allocated identity s.pool _ h update.vertex update.free update.colour
      update.result counter (by simpa only [StoredRepair.erase_node] using ha)
  | lowerCut u v live ratio charge retained =>
    simpa only [StoredRepair.replayStep, StoredRepair.erase_node] using
      allocated_poolUpdate ctx identity s.pool (s.lowerCut u v live ratio).pool
        (StoredTree.erasedChildren children) counter (by simpa only [StoredRepair.erase_node] using ha)
  | upperCut u v live ratio charge retained =>
    simpa only [StoredRepair.replayStep, StoredRepair.erase_node] using
      allocated_poolUpdate ctx identity s.pool (s.upperCut u v live ratio).pool
        (StoredTree.erasedChildren children) counter (by simpa only [StoredRepair.erase_node] using ha)

theorem replayStep_represents (ctx : Context n) (identity : ℕ) {s t : State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase)) :
    Represents (stepLedger identity step label children counter ledger)
      (ctx.plug (StoredRepair.node identity t
        (StoredRepair.replayStep identity step children hw ho counter).children).erase) := by
  cases step with
  | pin update =>
    let h : Parts s.pool (StoredTree.erasedChildren children) := parts (by simpa using hw)
    rw [replayStep_pin_shape identity update children hw ho counter h, StoredTree.erase_promotedNode]
    exact promotionLedger_represents ledger ctx identity s.pool _ h update.vertex update.free
      update.colour update.result counter (by simpa using ha) (by simpa using hrep) label
  | lowerCut u v live ratio charge retained =>
    simpa only [StoredRepair.replayStep, StoredRepair.erase_node, stepLedger] using
      represents_lowerCut ledger ctx identity s (StoredTree.erasedChildren children) u v live ratio
        (by simpa only [StoredRepair.erase_node] using hrep)
  | upperCut u v live ratio charge retained =>
    simpa only [StoredRepair.replayStep, StoredRepair.erase_node, stepLedger] using
      represents_upperCut ledger ctx identity s (StoredTree.erasedChildren children) u v live ratio
        (by simpa only [StoredRepair.erase_node] using hrep)

theorem replayStep_recorded (identity : ℕ) {s t : State n} (step : Step s t)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (calls : List (Option (Row n))) (hrecorded : Recorded calls (StoredRepair.node identity s children)) :
    Recorded calls (StoredRepair.node identity t
      (StoredRepair.replayStep identity step children hw ho counter).children) := by
  cases step with
  | pin update =>
    let h : Parts s.pool (StoredTree.erasedChildren children) := parts (by simpa using hw)
    rw [replayStep_pin_shape identity update children hw ho counter h]
    apply hrecorded.promotedNode h update.vertex update.free update.colour update.result
      ⟨update.data.rows, update.data.order⟩ _ counter
    intro x y hxy
    change update.data.rows.active x y = true at hxy
    rw [update.data.active_eq] at hxy
    exact SparseRepairGraph.eraseVertex_old _ _ x y hxy
  | lowerCut u v live ratio charge retained =>
    exact hrecorded.poolUpdate _ _ (Step.active_old (.lowerCut s u v live ratio charge retained))
  | upperCut u v live ratio charge retained =>
    exact hrecorded.poolUpdate _ _ (Step.active_old (.upperCut s u v live ratio charge retained))

theorem active_locations_free (ledger : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (s : State n) (children : List (ℕ × StoredTree n))
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase)) :
    ∀ u v, s.rows.active u v = true →
      (identity, u) ∈ ledger.free ∧ (identity, v) ∈ ledger.free := by
  intro u v huv
  have hroot : (identity, s.pool) ∈ PoolTreeTraversal.storedPools
      (ctx.plug (StoredRepair.node identity s children).erase) := by
    apply storedPools_mem_plug ctx
    rw [StoredRepair.erase_node, PoolTreeTraversal.storedPools]
    exact List.mem_cons_self
  have hf (x : Fin n) (hx : s.pool.pins x = none) : (identity, x) ∈ ledger.free := by
    rw [hrep.free]
    exact (mem_treeLocations _ _ _).mpr ⟨(identity, s.pool), hroot, rfl, (s.pool.free_iff x).mpr hx⟩
  exact ⟨hf u (s.active_free huv).1, hf v (s.active_free huv).2⟩

theorem run_stepActions (threshold : ℕ) (ctx : Context n) (identity : ℕ)
    {s t : State n} (step : Step s t) (label : StepLabel step)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (counter : ℕ) (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (E : Fin n → Fin n → Bool) (hsource : RecordedRows ledger.calls identity E)
    (hincident : step.IncidentFrom E)
    (hcurrent : RecordedRows ledger.calls identity s.rows.active)
    (hdegree : StepDegree threshold step label) :
    IncidenceLedger.run threshold ledger (stepActions identity step label children counter) =
      some (stepLedger identity step label children counter ledger) := by
  cases step with
  | pin update =>
    let h : Parts s.pool (StoredTree.erasedChildren children) := parts (by simpa using hw)
    obtain ⟨witness, hwitness⟩ := hsource.incident update.vertex hincident
    apply run_promotionActions threshold ledger ctx identity s.pool _ h update.vertex update.free
      update.colour update.result counter (by simpa using ha) (by simpa using hrep) label witness hwitness
    intro hkind
    exact (hdegree hkind).trans
      (hcurrent.degree_le_liveDegree (active_locations_free ledger ctx identity s children hrep) update.vertex)
  | lowerCut => rfl
  | upperCut => rfl

theorem stepLedger_calls (identity : ℕ) {s t : State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n)) (counter : ℕ)
    (ledger : IncidenceLedger.State n) :
    (stepLedger identity step label children counter ledger).calls = ledger.calls := by
  cases step <;> rfl

structure Log (n : ℕ) where
  ledger : IncidenceLedger.State n
  actions : List (Action n)

/-- Replay the exact same primitive steps and child updates as the runtime
tree replayer, emitting its actual chronological promotion/admission pairs. -/
def replayLedger (identity : ℕ) : {s t : State n} → (trace : Trace s t) → Labels trace →
    (children : List (ℕ × StoredTree n)) →
    (hw : (StoredRepair.node identity s children).erase.WellFormed) →
    (ho : (StoredRepair.node identity s children).erase.Coherent) →
    ℕ → IncidenceLedger.State n → Log n
  | _, _, .nil _, _, _, _, _, _, ledger => ⟨ledger, []⟩
  | _, _, .cons head tail, labels, children, hw, ho, counter, ledger =>
      let first := StoredRepair.replayStep identity head children hw ho counter
      let nextLedger := stepLedger identity head labels.1 children counter ledger
      let rest := replayLedger identity tail labels.2 first.children first.wellFormed first.coherent
        first.counter nextLedger
      ⟨rest.ledger, stepActions identity head labels.1 children counter ++ rest.actions⟩

theorem run_append (threshold : ℕ) (ledger : IncidenceLedger.State n)
    (before after : List (Action n)) :
    IncidenceLedger.run threshold ledger (before ++ after) =
      (IncidenceLedger.run threshold ledger before).bind (fun next => IncidenceLedger.run threshold next after) := by
  induction before generalizing ledger with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons_append, IncidenceLedger.run]
    cases hs : IncidenceLedger.step threshold ledger head with
    | none => rfl
    | some next => exact ih next

theorem replayLedger_calls (identity : ℕ) {s t : State n} (trace : Trace s t)
    (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent)
    (counter : ℕ) (ledger : IncidenceLedger.State n) :
    (replayLedger identity trace labels children hw ho counter ledger).ledger.calls = ledger.calls := by
  induction trace generalizing children counter ledger with
  | nil => rfl
  | cons head tail ih =>
    dsimp only [replayLedger]
    rw [ih, stepLedger_calls]

/-- All acceptance checks are discharged by the stored row history, actual
initial-graph incident witnesses, and the local degree selections. -/
theorem replayLedger_spec (threshold : ℕ) (ctx : Context n) (identity : ℕ)
    {s t : State n} (trace : Trace s t) (labels : Labels trace)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (hrecorded : Recorded ledger.calls (StoredRepair.node identity s children))
    (E : Fin n → Fin n → Bool) (hsource : RecordedRows ledger.calls identity E)
    (hincident : trace.IncidentFrom E) (hdegree : DegreeLabels threshold trace labels) :
    let actual := StoredRepair.replayTrace identity trace children hw ho counter
    let log := replayLedger identity trace labels children hw ho counter ledger
    IncidenceLedger.run threshold ledger log.actions = some log.ledger ∧
      Represents log.ledger (ctx.plug (StoredRepair.node identity t actual.children).erase) ∧
      Allocated (ctx.plug (StoredRepair.node identity t actual.children).erase) actual.counter ∧
      Recorded log.ledger.calls (StoredRepair.node identity t actual.children) := by
  induction trace generalizing children counter ledger with
  | nil => exact ⟨rfl, hrep, ha, hrecorded⟩
  | @cons s mid t head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    let nextLedger := stepLedger identity head labels.1 children counter ledger
    have hfirst_run := run_stepActions threshold ctx identity head labels.1 children hw counter ha
      ledger hrep E hsource hincident.1 hrecorded.here hdegree.1
    have hfirst_rep := replayStep_represents ctx identity head labels.1 children hw ho counter ha ledger hrep
    have hfirst_alloc := replayStep_allocated ctx identity head children hw ho counter ha
    have hfirst_recorded : Recorded nextLedger.calls (StoredRepair.node identity mid first.children) := by
      rw [stepLedger_calls]
      exact replayStep_recorded identity head children hw ho counter ledger.calls hrecorded
    have hnext_source : RecordedRows nextLedger.calls identity E := by
      rw [stepLedger_calls]
      exact hsource
    have hrest := ih labels.2 first.children first.wellFormed first.coherent first.counter hfirst_alloc
      nextLedger hfirst_rep hfirst_recorded hnext_source hincident.2 hdegree.2
    refine ⟨?_, hrest.2.1, hrest.2.2.1, hrest.2.2.2⟩
    change IncidenceLedger.run threshold ledger
      (stepActions identity head labels.1 children counter ++
        (replayLedger identity tail labels.2 first.children first.wellFormed first.coherent
          first.counter nextLedger).actions) = _
    rw [run_append, hfirst_run, Option.bind_some]
    exact hrest.1

/-- For the actual width-loop output, event kinds, degree checks, and source
witnesses are all supplied by its proved execution annotations. -/
theorem replay_width_result (threshold : ℕ) (ctx : Context n) (identity : ℕ)
    (s : State n) (p : ScaleParameters) (result : WidthResult s p)
    (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase))
    (hrecorded : Recorded ledger.calls (StoredRepair.node identity s children)) :
    let actual := StoredRepair.replayTrace identity result.trace children hw ho counter
    let log := replayLedger identity result.trace (widthLabels result.events) children hw ho counter ledger
    IncidenceLedger.run threshold ledger log.actions = some log.ledger ∧
      Represents log.ledger (ctx.plug (StoredRepair.node identity result.final actual.children).erase) ∧
      Allocated (ctx.plug (StoredRepair.node identity result.final actual.children).erase) actual.counter ∧
      Recorded log.ledger.calls (StoredRepair.node identity result.final actual.children) :=
  replayLedger_spec threshold ctx identity result.trace (widthLabels result.events) children hw ho counter ha
    ledger hrep hrecorded s.rows.active hrecorded.here result.incident
      (widthLabels_degreeLabels threshold result.events)

end SortingAdversary.Optimal.LedgerStoredReplay
