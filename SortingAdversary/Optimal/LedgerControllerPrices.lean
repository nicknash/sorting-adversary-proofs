import SortingAdversary.Optimal.LedgerRun
import SortingAdversary.Optimal.LedgerReplayPrices

/-!
# Signed receipt prices for actual controller queries

The runtime repair charge divides by the concrete child's birthday multiplier.
That multiplier dominates the emitted admission ordinal. Thus the logarithm
of the runtime charge is bounded by the signed receipt sum, whose credits are
exactly the increment of the global factorial potential.
-/

namespace SortingAdversary.Optimal.LedgerControllerPrices

open PoolState WidthRepair PoolTree.Tree TreeChronology LedgerTreeBridge LedgerTreeTransitions
open LedgerStoredReplay LedgerReplayLabels LedgerStructuralReplay LedgerBirthCredits LedgerReplayPrices
open LedgerQuery LedgerController LedgerRun RecursiveController ControllerMachine ControllerRun

variable {n : ℕ}

theorem step_log_charge (identity : ℕ) {s t : WidthRepair.State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    Real.log ((StoredRepair.replayStep identity step children hw ho counter).charge : ℝ) ≤
      (stepReceipt identity step label children counter).signed := by
  cases step with
  | pin update =>
    let h : Parts s.pool (StoredTree.erasedChildren children) := parts (by simpa using hw)
    let birthday := admissionNumber update.result (StoredTree.erasedChildren children)
    let multiplier := birthMultiplier h update.vertex update.free update.colour update.result
    have hb : (0 : ℝ) < birthday := by
      exact_mod_cast admissionNumber_pos update.result (StoredTree.erasedChildren children)
    have hm : (0 : ℝ) < multiplier := by
      exact_mod_cast birthMultiplier_pos h update.vertex update.free update.colour update.result
    have hc : (0 : ℝ) < update.charge := by exact_mod_cast (Step.pin update).charge_pos
    have hbm : (birthday : ℝ) ≤ multiplier := by
      exact_mod_cast admissionNumber_le_multiplier h update.vertex update.free update.colour update.result
    change Real.log (((update.charge / multiplier : ℚ) : ℝ)) ≤
      Real.log (update.charge : ℝ) - Real.log (birthday : ℝ)
    rw [Rat.cast_div, Rat.cast_natCast, Real.log_div hc.ne' hm.ne']
    exact sub_le_sub_left (Real.log_le_log hb hbm) _
  | lowerCut => simp only [StoredRepair.replayStep, stepReceipt, Receipt.signed, Receipt.debit,
      Receipt.credit, Nat.cast_one, Real.log_one, sub_zero, le_refl]
  | upperCut => simp only [StoredRepair.replayStep, stepReceipt, Receipt.signed, Receipt.debit,
      Receipt.credit, Nat.cast_one, Real.log_one, sub_zero, le_refl]

theorem replay_log_charge (identity : ℕ) {s t : WidthRepair.State n} (trace : Trace s t)
    (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    Real.log ((StoredRepair.replayTrace identity trace children hw ho counter).charge : ℝ) ≤
      ((replayReceipts identity trace labels children hw ho counter).map Receipt.signed).sum := by
  induction trace generalizing children counter with
  | nil => simp [StoredRepair.replayTrace, replayReceipts]
  | cons head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    let rest := StoredRepair.replayTrace identity tail first.children first.wellFormed first.coherent first.counter
    have hf : (0 : ℝ) < first.charge := by exact_mod_cast first.charge_pos
    have hr : (0 : ℝ) < rest.charge := by exact_mod_cast rest.charge_pos
    have hh := step_log_charge identity head labels.1 children hw ho counter
    have ht := ih labels.2 first.children first.wellFormed first.coherent first.counter
    change Real.log ((first.charge * rest.charge : ℚ) : ℝ) ≤ _
    rw [Rat.cast_mul, Real.log_mul hf.ne' hr.ne']
    simpa only [replayReceipts, List.map_cons, List.sum_cons] using add_le_add hh ht

def recordReceipts {p : Parameters} (record : RepairRecord p n) : List (Receipt n) :=
  replayReceipts record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter

def responseReceipts {p : Parameters} (s : Active p n) (q : Query n) : List (Receipt n) :=
  match (respond s q).record with
  | none => []
  | some record => recordReceipts record

theorem record_credit {p : Parameters} (record : RepairRecord p n) (ledger : IncidenceLedger.State n)
    (origin : Origin record ledger) :
    factorialCredit (recordLog record ledger).ledger = factorialCredit ledger +
      ((recordReceipts record).map Receipt.credit).sum := by
  obtain ⟨ctx, ha, hrep, _⟩ := origin
  let after := compared record.before record.first record.second record.first_member record.second_member
    record.distinct record.updated
  let called := physicalLedger ledger (physicalRow record)
  have ha' : Allocated (ctx.plug (StoredRepair.node record.identity after record.children).erase)
      record.counter := by
    rw [StoredRepair.erase_node]
    apply allocated_poolUpdate ctx record.identity record.before.pool after.pool _ record.counter
    simpa only [StoredRepair.erase_node] using ha
  have hrep' : Represents called (ctx.plug (StoredRepair.node record.identity after record.children).erase) := by
    rw [StoredRepair.erase_node]
    apply represents_poolUpdate called ctx record.identity record.before.pool after.pool _ rfl rfl
    simpa only [StoredRepair.erase_node] using physicalLedger_represents ledger _ (physicalRow record) hrep
  exact replayReceipts_credit ctx record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter ha' called hrep'

theorem record_log_charge {p : Parameters} (record : RepairRecord p n) :
    Real.log (record.replay.charge : ℝ) ≤ ((recordReceipts record).map Receipt.signed).sum :=
  replay_log_charge record.identity record.result.trace (structuralLabels record.result.events)
    record.children record.wellFormed record.coherent record.counter

noncomputable def physicalPrice (p : Parameters) : ℝ := Real.log ((1 / (1 / 2 - p.error) : ℚ) : ℝ)

theorem physicalPrice_nonneg (p : Parameters) : 0 ≤ physicalPrice p := by
  apply Real.log_nonneg
  have hd : (0 : ℚ) < 1 / 2 - p.error := sub_pos.mpr p.error_small
  have hh : (1 : ℚ) ≤ 1 / (1 / 2 - p.error) := (le_div_iff₀ hd).mpr (by linarith [p.error_pos])
  exact_mod_cast hh

theorem response_charge_pos {p : Parameters} (s : Active p n) (q : Query n) :
    0 < (respond s q).charge := by
  have hb : (0 : ℚ) < s.tree.erase.count := by exact_mod_cast s.tree.erase.count_pos
  have ha : (0 : ℚ) < (respond s q).next.tree.erase.count := by
    exact_mod_cast (respond s q).next.tree.erase.count_pos
  exact pos_of_mul_pos_left (hb.trans_le (respond s q).retention) ha.le

theorem response_log_loss {p : Parameters} (s : Active p n) (q : Query n) :
    Real.log (s.tree.erase.count : ℝ) - Real.log ((respond s q).next.tree.erase.count : ℝ) ≤
      Real.log ((respond s q).charge : ℝ) := by
  have hb : (0 : ℝ) < s.tree.erase.count := by exact_mod_cast s.tree.erase.count_pos
  have ha : (0 : ℝ) < (respond s q).next.tree.erase.count := by
    exact_mod_cast (respond s q).next.tree.erase.count_pos
  have hp : (0 : ℝ) < (respond s q).charge := by exact_mod_cast response_charge_pos s q
  have hr : (s.tree.erase.count : ℝ) ≤ ((respond s q).charge : ℝ) * (respond s q).next.tree.erase.count := by
    exact_mod_cast (respond s q).retention
  have hl := Real.log_le_log hb hr
  rw [Real.log_mul hp.ne' ha.ne'] at hl
  linarith

theorem response_credit (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    (s : Active p n) (q : Query n) (ledger : IncidenceLedger.State n)
    (halloc : Allocated s.tree.erase s.counter) (hrep : Represents ledger s.tree.erase)
    (hrecorded : LedgerStoredHistory.Recorded ledger.calls s.tree) :
    factorialCredit (responseLog s q ledger).ledger = factorialCredit ledger +
      ((responseReceipts s q).map Receipt.credit).sum := by
  have hs := LedgerController.respond_spec threshold hthreshold s q ledger halloc hrep hrecorded
  cases hr : (respond s q).record with
  | none =>
    simp only [responseLog, logFor, hr, responseReceipts, List.map_nil, List.sum_nil, add_zero]
    rfl
  | some record =>
    simp only [responseLog, logFor, hr, responseReceipts]
    exact record_credit record ledger (hs.origin record hr)

theorem response_signed (threshold : ℕ) {p : Parameters} (hthreshold : threshold ≤ p.repair.D)
    (s : Active p n) (q : Query n) (ledger : IncidenceLedger.State n)
    (halloc : Allocated s.tree.erase s.counter) (hrep : Represents ledger s.tree.erase)
    (hrecorded : LedgerStoredHistory.Recorded ledger.calls s.tree) :
    Real.log (s.tree.erase.count : ℝ) - Real.log ((respond s q).next.tree.erase.count : ℝ) ≤
      physicalPrice p + ((responseReceipts s q).map Receipt.debit).sum -
        (factorialCredit (responseLog s q ledger).ledger - factorialCredit ledger) := by
  have hs := LedgerController.respond_spec threshold hthreshold s q ledger halloc hrep hrecorded
  have hc := response_credit threshold hthreshold s q ledger halloc hrep hrecorded
  have hp : Real.log ((respond s q).charge : ℝ) ≤
      physicalPrice p + ((responseReceipts s q).map Receipt.signed).sum := by
    cases hr : (respond s q).record with
    | none =>
      have he := hs.charge
      rw [hr] at he
      rw [he]
      simpa only [Rat.cast_one, Real.log_one, responseReceipts, hr, List.map_nil, List.sum_nil, add_zero] using
        physicalPrice_nonneg p
    | some record =>
      have he := hs.charge
      rw [hr] at he
      have hf : (0 : ℝ) < ((1 / (1 / 2 - p.error) : ℚ) : ℝ) := by
        exact_mod_cast (div_pos (by norm_num : (0 : ℚ) < 1) (sub_pos.mpr p.error_small))
      have hj : (0 : ℝ) < record.replay.charge := by exact_mod_cast record.replay.charge_pos
      rw [he, Rat.cast_mul, Real.log_mul hf.ne' hj.ne']
      simpa only [responseReceipts, hr, physicalPrice, add_comm] using add_le_add_left (record_log_charge record)
        (physicalPrice p)
  rw [sum_signed] at hp
  have hl := response_log_loss s q
  linarith

end SortingAdversary.Optimal.LedgerControllerPrices
