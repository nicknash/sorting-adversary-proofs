import SortingAdversary.Optimal.ControllerLedgerAlignment
import SortingAdversary.Optimal.ControllerPriceSum
import SortingAdversary.Optimal.StoredStateIndex

/-!
# The actual hub history in the final finite node dictionary

Only proof bookkeeping converts immutable natural node identities into final
preorder indices. Each record still carries its actual historical block and
its immutable colour identity. Accepted physical promotions prove distinct
locations, which bounds every destination count by its actual pin fibre.
-/

namespace SortingAdversary.Optimal.IndexedHubHistory

open scoped BigOperators
open WidthRepair PoolState PoolTreeGroups StoredEvolution StoredStateIndex TreeChronology
open RecursiveController ControllerMachine ControllerRun ControllerPricing RepairPricing

variable {n : ℕ}

noncomputable def lookup (tree : StoredTree n) (identity : ℕ) : StateIndex tree :=
  if h : ∃ i : StateIndex tree, identityAt tree i = identity then Classical.choose h
  else ⟨0, storedStates_nonempty tree⟩

theorem lookup_at (tree : StoredTree n) {counter : ℕ} (allocated : Allocated tree.erase counter)
    (i : StateIndex tree) : lookup tree (identityAt tree i) = i := by
  rw [lookup, dif_pos ⟨i, rfl⟩]
  apply identityAt_injective tree allocated
  exact Classical.choose_spec (show ∃ j, identityAt tree j = identityAt tree i from ⟨i, rfl⟩)

theorem lookup_occurs {tree : StoredTree n} {counter identity : ℕ} {state : State n}
    (allocated : Allocated tree.erase counter) (occurs : NodeAt tree identity state) :
    identityAt tree (lookup tree identity) = identity ∧ stateAt tree (lookup tree identity) = state := by
  have hi := lookup_at tree allocated (locate occurs)
  rw [locate_identity] at hi
  rw [hi]
  exact ⟨locate_identity occurs, locate_state occurs⟩

noncomputable def events (tree : StoredTree n) (history : List (ℕ × HubEvent n)) :
    GlobalHistory.Events (StateIndex tree) n history.length :=
  fun i => (lookup tree (history.get i).1, (history.get i).2)

def AtFinal (tree : StoredTree n) (history : List (ℕ × HubEvent n)) : Prop :=
  ∀ tagged ∈ history, ∃ state, NodeAt tree tagged.1 state ∧ tagged.2.Fits state

theorem events_fits (tree : StoredTree n) {counter : ℕ} (allocated : Allocated tree.erase counter)
    (history : List (ℕ × HubEvent n)) (fits : AtFinal tree history) (i : Fin history.length) :
    (events tree history i).2.Fits (stateAt tree (events tree history i).1) := by
  obtain ⟨state, occurs, h⟩ := fits (history.get i) (List.get_mem _ _)
  change (history.get i).2.Fits (stateAt tree (lookup tree (history.get i).1))
  rw [(lookup_occurs allocated occurs).2]
  exact h

theorem events_identity (tree : StoredTree n) {counter : ℕ} (allocated : Allocated tree.erase counter)
    (history : List (ℕ × HubEvent n)) (fits : AtFinal tree history) (i : Fin history.length) :
    identityAt tree (events tree history i).1 = (history.get i).1 := by
  obtain ⟨state, occurs, _⟩ := fits (history.get i) (List.get_mem _ _)
  exact (lookup_occurs allocated occurs).1

theorem events_locations_injective (tree : StoredTree n) {counter : ℕ}
    (allocated : Allocated tree.erase counter) (history : List (ℕ × HubEvent n))
    (fits : AtFinal tree history)
    (nodup : (history.map (fun tagged => (tagged.1, tagged.2.vertex))).Nodup) :
    Function.Injective (fun i => ((events tree history i).1, (events tree history i).2.vertex)) := by
  intro i j hij
  have hh := congrArg (fun pair => (identityAt tree pair.1, pair.2)) hij
  rw [events_identity tree allocated history fits i, events_identity tree allocated history fits j] at hh
  apply Fin.ext
  apply (nodup.getElem_inj_iff (hi := by simpa using i.isLt) (hj := by simpa using j.isLt)).mp
  simpa only [List.getElem_map, List.get_eq_getElem, events] using hh

theorem fits_identity_lt {event : HubEvent n} {state : State n} (fits : event.Fits state) :
    event.identity < state.pool.palette + 1 := by
  obtain ⟨colour, _, he⟩ := fits.pinned
  rw [← he]
  exact (state.order.symm colour).isLt

theorem countAt_le_pinFiber {Node : Type*} [DecidableEq Node] {H : ℕ}
    (final : Node → State n) (history : GlobalHistory.Events Node n H)
    (fits : ∀ i, (history i).2.Fits (final (history i).1))
    (unique : Function.Injective (fun i => ((history i).1, (history i).2.vertex)))
    (node : Node) (colour : Fin ((final node).pool.palette + 1)) :
    GlobalHistory.countAt history (node, colour.val) ≤
      (pinFiber (final node).pool ((final node).order colour)).card := by
  unfold GlobalHistory.countAt
  apply Finset.card_le_card_of_injOn (fun i => (history i).2.vertex)
  · intro i hi
    have hd := (Finset.mem_filter.mp hi).2
    have hn := congrArg Prod.fst hd
    have hc := congrArg Prod.snd hd
    have hf := fits i
    rw [hn] at hf
    obtain ⟨actual, hp, he⟩ := hf.pinned
    have heq : (final node).order.symm actual = colour := Fin.ext (he.trans hc)
    have hr := congrArg (final node).order heq
    simp only [Equiv.apply_symm_apply] at hr
    apply Finset.mem_filter.mpr
    exact ⟨hf.member, hp.trans (congrArg some hr)⟩
  · intro i hi j hj hvertex
    apply unique
    apply Prod.ext
    · exact (congrArg Prod.fst (Finset.mem_filter.mp hi).2).trans
        (congrArg Prod.fst (Finset.mem_filter.mp hj).2).symm
    · exact hvertex

theorem countAt_le_capacity {Node : Type*} [DecidableEq Node] {H : ℕ}
    (final : Node → State n) (exponent : Node → ℕ) (history : GlobalHistory.Events Node n H)
    (fits : ∀ i, (history i).2.Fits (final (history i).1))
    (unique : Function.Injective (fun i => ((history i).1, (history i).2.vertex)))
    (cap : ∀ node, (final node).pool.palette + 1 ≤ 2 ^ exponent node)
    (destination : Node × ℕ) (member : destination ∈ GlobalHistory.destinations history) :
    GlobalHistory.countAt history destination ≤ 2 ^ exponent destination.1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp member
  have hid : (history i).1 = destination.1 := congrArg Prod.fst hi
  have hc : (history i).2.identity = destination.2 := congrArg Prod.snd hi
  have hcolour := fits_identity_lt (fits i)
  rw [hid, hc] at hcolour
  let colour : Fin ((final destination.1).pool.palette + 1) := ⟨destination.2, hcolour⟩
  have hb := countAt_le_pinFiber final history fits unique destination.1 colour
  exact hb.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans
    ((final destination.1).pool.capacity.trans (cap destination.1)))

noncomputable def exponentByIdentity (tree : StoredTree n) (exponent : StateIndex tree → ℕ) : ℕ → ℕ :=
  fun identity => exponent (lookup tree identity)

theorem price_sum (tree : StoredTree n) (history : List (ℕ × HubEvent n))
    (exponent : StateIndex tree → ℕ) :
    (∑ i : Fin history.length, (events tree history i).2.unitPrice (exponent (events tree history i).1)) =
      (history.map (hubPrice (exponentByIdentity tree exponent))).sum := by
  rw [PoolTreeAccounting.sum_map_get]
  rfl

theorem run_record_capacity {p : Parameters} {s final : Active p n} {history : History n}
    (run : ActiveRun p s history final) (allocated : Allocated final.tree.erase final.counter)
    (exponent : StateIndex final.tree → ℕ)
    (cap : ∀ i, (stateAt final.tree i).pool.palette + 1 ≤ 2 ^ exponent i)
    (record : RepairRecord p n) (member : record ∈ runRecords s history) :
    record.result.final.pool.palette + 1 ≤ 2 ^ exponentByIdentity final.tree exponent record.identity := by
  obtain ⟨state, occurs, evolution⟩ := runRecords_final run record member
  have he := (lookup_occurs allocated occurs).2
  have hc := cap (lookup final.tree record.identity)
  rw [he] at hc
  exact (evolution_order evolution).births.trans hc

/-- The signed dictionary estimate now applies to the actual complete run,
with physical uniqueness and destination population bounds proved here. -/
theorem actual_signed_hubs (p : Parameters) (N : ℕ)
    {final : Active p (N + 2)} {history : History (N + 2)}
    (run : ActiveRun p (initialActive p N) history final)
    (exponent : StateIndex final.tree → ℕ)
    (cap : ∀ i, (stateAt final.tree i).pool.palette + 1 ≤ 2 ^ exponent i) :
    let actual := events final.tree (runHubs (initialActive p N) history)
    (∑ i, (actual i).2.unitPrice (exponent (actual i).1)) -
      (∑ c ∈ GlobalHistory.destinations actual, Real.log ((GlobalHistory.countAt actual c).factorial : ℝ)) ≤
      SignedPrice.priceCoefficient (Real.exp 1 * 128) *
        SignedPrice.entropyEnvelope (runHubs (initialActive p N) history).length
          ((DyadicDictionary.totalCapacity exponent : ℝ) +
            ∑ c ∈ GlobalHistory.destinations actual, (GlobalHistory.countAt actual c : ℝ) *
              Real.log ((2 : ℝ) ^ exponent c.1 / GlobalHistory.countAt actual c)) := by
  let allocated := (LedgerRun.initial_spec p N run).allocated
  have hf : AtFinal final.tree (runHubs (initialActive p N) history) := runHubs_fit run
  let actual := events final.tree (runHubs (initialActive p N) history)
  have fits := events_fits final.tree allocated _ hf
  have unique := events_locations_injective final.tree allocated _ hf
    (ControllerLedgerAlignment.actual_hub_locations_nodup p N run)
  exact GlobalHistory.signed_debit_le (stateAt final.tree) exponent actual fits cap
    (countAt_le_capacity _ exponent actual fits unique cap)

end SortingAdversary.Optimal.IndexedHubHistory
