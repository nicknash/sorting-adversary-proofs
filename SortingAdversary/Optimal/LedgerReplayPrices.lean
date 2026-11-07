import SortingAdversary.Optimal.LedgerBirthCredits

/-!
# Concrete repair receipts and signed birthday accounting

Every receipt is computed from a primitive step, its actual classification,
and the destination child present at that instant. The complete replayer
emits these receipts in chronological order. Their credit sum is exactly the
change in the ledger's factorial potential, and their signed sum bounds the
actual loss of the stored tree's counting potential.
-/

namespace SortingAdversary.Optimal.LedgerReplayPrices

open PoolState WidthRepair PoolTree.Tree TreeChronology LedgerTreeBridge
open LedgerTreeTransitions LedgerStoredReplay LedgerReplayLabels LedgerBirthCredits
open IncidenceLedger (Kind)

variable {n : ℕ}

structure Receipt (n : ℕ) where
  parent : ℕ
  child : Option ℕ
  vertex : Option (Fin n)
  kind : Option Kind
  birthday : ℕ
  charge : ℚ

def stepReceipt (identity : ℕ) {s t : State n} (step : Step s t) (label : StepLabel step)
    (children : List (ℕ × StoredTree n)) (counter : ℕ) : Receipt n :=
  match step, label with
  | .pin update, kind =>
      ⟨identity, some (receivingIdentity update.result (StoredTree.erasedChildren children) counter),
        some update.vertex, some kind, admissionNumber update.result (StoredTree.erasedChildren children),
        update.charge⟩
  | .lowerCut _ _ _ _ _ charge _, _ => ⟨identity, none, none, none, 1, charge⟩
  | .upperCut _ _ _ _ _ charge _, _ => ⟨identity, none, none, none, 1, charge⟩

noncomputable def Receipt.credit (receipt : Receipt n) : ℝ := Real.log (receipt.birthday : ℝ)
noncomputable def Receipt.debit (receipt : Receipt n) : ℝ := Real.log (receipt.charge : ℝ)
noncomputable def Receipt.signed (receipt : Receipt n) : ℝ := receipt.debit - receipt.credit

theorem stepReceipt_charge (identity : ℕ) {s t : State n} (step : Step s t) (label : StepLabel step)
    (children : List (ℕ × StoredTree n)) (counter : ℕ) :
    (stepReceipt identity step label children counter).charge = step.charge := by
  cases step <;> rfl

theorem stepReceipt_birthday_pos (identity : ℕ) {s t : State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n)) (counter : ℕ) :
    0 < (stepReceipt identity step label children counter).birthday := by
  cases step with
  | pin update => exact admissionNumber_pos update.result (StoredTree.erasedChildren children)
  | lowerCut => exact Nat.zero_lt_one
  | upperCut => exact Nat.zero_lt_one

theorem stepReceipt_credit (ctx : Context n) (identity : ℕ) {s t : State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase)) :
    factorialCredit (stepLedger identity step label children counter ledger) =
      factorialCredit ledger + (stepReceipt identity step label children counter).credit := by
  cases step with
  | pin update =>
    let h : Parts s.pool (StoredTree.erasedChildren children) := parts (by simpa using hw)
    exact promotionLedger_credit ledger ctx identity s.pool _ h update.vertex update.free update.colour
      update.result counter (by simpa using ha) (by simpa using hrep) label
  | lowerCut => simp only [stepLedger, stepReceipt, Receipt.credit, Nat.cast_one, Real.log_one, add_zero]
  | upperCut => simp only [stepLedger, stepReceipt, Receipt.credit, Nat.cast_one, Real.log_one, add_zero]

theorem stepReceipt_retention (identity : ℕ) {s t : State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    ((stepReceipt identity step label children counter).birthday : ℚ) *
        (StoredRepair.node identity s children).erase.count ≤
      (stepReceipt identity step label children counter).charge *
        (StoredRepair.node identity t
          (StoredRepair.replayStep identity step children hw ho counter).children).erase.count := by
  cases step with
  | pin update =>
    let oldChildren := StoredTree.erasedChildren children
    let h : Parts s.pool oldChildren := parts (by simpa [oldChildren] using hw)
    let birthday := admissionNumber update.result oldChildren
    let multiplier := birthMultiplier h update.vertex update.free update.colour update.result
    let childCount : ℕ := (oldChildren.map (fun a => a.2.count)).prod
    have hb : (birthday : ℚ) ≤ multiplier := by
      exact_mod_cast admissionNumber_le_multiplier h update.vertex update.free update.colour update.result
    rw [replayStep_pin_shape identity update children hw ho counter h, StoredTree.erase_promotedNode,
      StoredRepair.erase_node, promotedNode_count, count]
    change (birthday : ℚ) * ((s.pool.system.count * childCount : ℕ) : ℚ) ≤
      update.charge * ((update.result.system.count * childCount * multiplier : ℕ) : ℚ)
    simp only [Nat.cast_mul]
    calc
      _ ≤ (multiplier : ℚ) * ((s.pool.system.count : ℚ) * (childCount : ℚ)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (multiplier : ℚ) * ((update.charge * update.result.system.count) * (childCount : ℚ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right update.retained (by positivity))
          (Nat.cast_nonneg _)
      _ = _ := by ring
  | lowerCut u v live ratio charge retained =>
    simpa only [stepReceipt, Nat.cast_one, one_mul, StoredRepair.replayStep] using
      (StoredRepair.replayStep identity (.lowerCut s u v live ratio charge retained) children hw ho counter).retention
  | upperCut u v live ratio charge retained =>
    simpa only [stepReceipt, Nat.cast_one, one_mul, StoredRepair.replayStep] using
      (StoredRepair.replayStep identity (.upperCut s u v live ratio charge retained) children hw ho counter).retention

theorem stepReceipt_signed (identity : ℕ) {s t : State n} (step : Step s t)
    (label : StepLabel step) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    Real.log ((StoredRepair.node identity s children).erase.count : ℝ) -
        Real.log ((StoredRepair.node identity t
          (StoredRepair.replayStep identity step children hw ho counter).children).erase.count : ℝ) ≤
      (stepReceipt identity step label children counter).signed := by
  let receipt := stepReceipt identity step label children counter
  let before := (StoredRepair.node identity s children).erase.count
  let after := (StoredRepair.node identity t
    (StoredRepair.replayStep identity step children hw ho counter).children).erase.count
  have hb : (0 : ℝ) < receipt.birthday := by exact_mod_cast stepReceipt_birthday_pos identity step label children counter
  have hc : (0 : ℝ) < receipt.charge := by
    change (0 : ℝ) < (stepReceipt identity step label children counter).charge
    rw [stepReceipt_charge]
    exact_mod_cast step.charge_pos
  have hbefore : (0 : ℝ) < before := by exact_mod_cast (StoredRepair.node identity s children).erase.count_pos
  have hafter : (0 : ℝ) < after := by exact_mod_cast (StoredRepair.node identity t
    (StoredRepair.replayStep identity step children hw ho counter).children).erase.count_pos
  have hr : (receipt.birthday : ℝ) * before ≤ (receipt.charge : ℝ) * after := by
    exact_mod_cast stepReceipt_retention identity step label children hw ho counter
  have hlog := Real.log_le_log (mul_pos hb hbefore) hr
  rw [Real.log_mul hb.ne' hbefore.ne', Real.log_mul hc.ne' hafter.ne'] at hlog
  change Real.log (before : ℝ) - Real.log (after : ℝ) ≤
    Real.log (receipt.charge : ℝ) - Real.log (receipt.birthday : ℝ)
  linarith

def replayReceipts (identity : ℕ) : {s t : State n} → (trace : Trace s t) → Labels trace →
    (children : List (ℕ × StoredTree n)) →
    (hw : (StoredRepair.node identity s children).erase.WellFormed) →
    (ho : (StoredRepair.node identity s children).erase.Coherent) → ℕ → List (Receipt n)
  | _, _, .nil _, _, _, _, _, _ => []
  | _, _, .cons head tail, labels, children, hw, ho, counter =>
      let first := StoredRepair.replayStep identity head children hw ho counter
      stepReceipt identity head labels.1 children counter ::
        replayReceipts identity tail labels.2 first.children first.wellFormed first.coherent first.counter

theorem replayReceipts_length (identity : ℕ) {s t : State n} (trace : Trace s t)
    (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    (replayReceipts identity trace labels children hw ho counter).length = trace.length := by
  induction trace generalizing children counter with
  | nil => rfl
  | cons head tail ih =>
    simp only [replayReceipts, List.length_cons, Trace.length, ih]

theorem replayReceipts_credit (ctx : Context n) (identity : ℕ) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase)) :
    factorialCredit (replayLedger identity trace labels children hw ho counter ledger).ledger =
      factorialCredit ledger +
        ((replayReceipts identity trace labels children hw ho counter).map Receipt.credit).sum := by
  induction trace generalizing children counter ledger with
  | nil => simp [replayLedger, replayReceipts]
  | cons head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    let nextLedger := stepLedger identity head labels.1 children counter ledger
    have ha' := replayStep_allocated ctx identity head children hw ho counter ha
    have hrep' := replayStep_represents ctx identity head labels.1 children hw ho counter ha ledger hrep
    have htail := ih labels.2 first.children first.wellFormed first.coherent first.counter ha'
      nextLedger hrep'
    have hhead := stepReceipt_credit ctx identity head labels.1 children hw counter ha ledger hrep
    dsimp only [replayLedger, replayReceipts]
    simp only [List.map_cons, List.sum_cons]
    rw [htail, hhead]
    ring

theorem replayReceipts_signed (identity : ℕ) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ) :
    Real.log ((StoredRepair.node identity s children).erase.count : ℝ) -
        Real.log ((StoredRepair.node identity t
          (StoredRepair.replayTrace identity trace children hw ho counter).children).erase.count : ℝ) ≤
      ((replayReceipts identity trace labels children hw ho counter).map Receipt.signed).sum := by
  induction trace generalizing children counter with
  | nil => simp [StoredRepair.replayTrace, replayReceipts]
  | cons head tail ih =>
    let first := StoredRepair.replayStep identity head children hw ho counter
    have htail := ih labels.2 first.children first.wellFormed first.coherent first.counter
    have hhead := stepReceipt_signed identity head labels.1 children hw ho counter
    dsimp only [StoredRepair.replayTrace, replayReceipts]
    simp only [List.map_cons, List.sum_cons]
    linarith

theorem sum_signed (receipts : List (Receipt n)) :
    (receipts.map Receipt.signed).sum = (receipts.map Receipt.debit).sum - (receipts.map Receipt.credit).sum := by
  induction receipts with
  | nil => simp
  | cons receipt rest ih =>
    simp only [List.map_cons, List.sum_cons, Receipt.signed, ih]
    ring

/-- The entire actual repair loses at most its parent debits minus the exact
factorial credit created by its real recursive child admissions. -/
theorem replay_signed_factorial (ctx : Context n) (identity : ℕ) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase)) :
    let actual := StoredRepair.replayTrace identity trace children hw ho counter
    let log := replayLedger identity trace labels children hw ho counter ledger
    let receipts := replayReceipts identity trace labels children hw ho counter
    Real.log ((StoredRepair.node identity s children).erase.count : ℝ) -
        Real.log ((StoredRepair.node identity t actual.children).erase.count : ℝ) ≤
      (receipts.map Receipt.debit).sum - (factorialCredit log.ledger - factorialCredit ledger) := by
  have hc := replayReceipts_credit ctx identity trace labels children hw ho counter ha ledger hrep
  have hp := replayReceipts_signed identity trace labels children hw ho counter
  rw [sum_signed] at hp
  dsimp only
  linarith

def countFactor : Context n → ℕ
  | .top => 1
  | .child _ p before _ after outer => p.system.count *
      (before.map (fun a => a.2.count)).prod * (after.map (fun a => a.2.count)).prod * countFactor outer

theorem context_count (ctx : Context n) (t : PoolTree.Tree n) :
    (ctx.plug t).count = t.count * countFactor ctx := by
  induction ctx generalizing t with
  | top => simp [Context.plug, countFactor]
  | child identity p before key after outer ih =>
    rw [Context.plug, ih, count]
    simp only [countFactor, List.map_append, List.prod_append, List.map_cons, List.prod_cons]
    ring

theorem countFactor_pos (ctx : Context n) : 0 < countFactor ctx := by
  have hforest (children : List (ℕ × PoolTree.Tree n)) :
      0 < (children.map (fun a => a.2.count)).prod := by
    apply List.prod_pos
    intro k hk
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hk
    exact a.2.count_pos
  induction ctx with
  | top => exact Nat.zero_lt_one
  | child identity p before key after outer ih =>
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p.count_pos (hforest before)) (hforest after)) ih

theorem log_count_context_difference (ctx : Context n) (before after : PoolTree.Tree n) :
    Real.log ((ctx.plug before).count : ℝ) - Real.log ((ctx.plug after).count : ℝ) =
      Real.log (before.count : ℝ) - Real.log (after.count : ℝ) := by
  have hb : (before.count : ℝ) ≠ 0 := by exact_mod_cast before.count_pos.ne'
  have ha : (after.count : ℝ) ≠ 0 := by exact_mod_cast after.count_pos.ne'
  have hc : (countFactor ctx : ℝ) ≠ 0 := by exact_mod_cast (countFactor_pos ctx).ne'
  rw [context_count, context_count, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul hb hc, Real.log_mul ha hc]
  ring

/-- The signed accounting applies to the full global tree when a repair is
performed at any stored descendant selected by the concrete recursion stack. -/
theorem replay_signed_factorial_global (ctx : Context n) (identity : ℕ) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) (children : List (ℕ × StoredTree n))
    (hw : (StoredRepair.node identity s children).erase.WellFormed)
    (ho : (StoredRepair.node identity s children).erase.Coherent) (counter : ℕ)
    (ha : Allocated (ctx.plug (StoredRepair.node identity s children).erase) counter)
    (ledger : IncidenceLedger.State n)
    (hrep : Represents ledger (ctx.plug (StoredRepair.node identity s children).erase)) :
    let actual := StoredRepair.replayTrace identity trace children hw ho counter
    let log := replayLedger identity trace labels children hw ho counter ledger
    let receipts := replayReceipts identity trace labels children hw ho counter
    Real.log ((ctx.plug (StoredRepair.node identity s children).erase).count : ℝ) -
        Real.log ((ctx.plug (StoredRepair.node identity t actual.children).erase).count : ℝ) ≤
      (receipts.map Receipt.debit).sum - (factorialCredit log.ledger - factorialCredit ledger) := by
  dsimp only
  rw [log_count_context_difference]
  exact replay_signed_factorial ctx identity trace labels children hw ho counter ha ledger hrep

end SortingAdversary.Optimal.LedgerReplayPrices
