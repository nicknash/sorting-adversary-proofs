import SortingAdversary.Optimal.LedgerStoredReplay

/-!
# Actual receiving admission numbers and exact factorial credits

Each receiving location is new in the chronological ledger. Its admission
number is computed from the labels already entered at that immutable child.
The actual tree birthday multiplier dominates this number. A single
admission increases the finite log-factorial potential by exactly its log,
so chronological summation needs no externally supplied birthday schedule.
-/

namespace SortingAdversary.Optimal.LedgerBirthCredits

open scoped BigOperators
open PoolState PoolTree PoolTree.Tree PoolTreeTraversal TreeChronology
open LedgerTreeBridge LedgerTreeTransitions LedgerStoredReplay

variable {n : ℕ}

set_option maxHeartbeats 600000

def enteredCount (ledger : IncidenceLedger.State n) (identity : ℕ) : ℕ :=
  (ledger.entered.filter (fun location => location.1 = identity)).card

def ordinal (ledger : IncidenceLedger.State n) (identity : ℕ) : ℕ := enteredCount ledger identity + 1

def creditNodes (ledger : IncidenceLedger.State n) : Finset ℕ := ledger.entered.image Prod.fst

noncomputable def factorialCredit (ledger : IncidenceLedger.State n) : ℝ :=
  ∑ identity ∈ creditNodes ledger, Real.log ((enteredCount ledger identity).factorial : ℝ)

theorem enteredCount_insert {before after : IncidenceLedger.State n}
    (location : IncidenceLedger.Location n) (he : after.entered = insert location before.entered)
    (hnew : location ∉ before.entered) (identity : ℕ) :
    enteredCount after identity =
      if identity = location.1 then enteredCount before identity + 1 else enteredCount before identity := by
  by_cases hid : identity = location.1
  · subst identity
    have hn : location ∉ before.entered.filter (fun x => x.1 = location.1) :=
      fun h => hnew (Finset.mem_filter.mp h).1
    simp [enteredCount, he, Finset.filter_insert, hn]
  · have hne : location.1 ≠ identity := Ne.symm hid
    simp only [enteredCount, he, Finset.filter_insert, if_neg hne, if_neg hid]

theorem enteredCount_zero_of_not_creditNodes (ledger : IncidenceLedger.State n) (identity : ℕ)
    (h : identity ∉ creditNodes ledger) : enteredCount ledger identity = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro location hl
  obtain ⟨he, hid⟩ := Finset.mem_filter.mp hl
  exact h (Finset.mem_image.mpr ⟨location, he, hid⟩)

theorem creditNodes_insert {before after : IncidenceLedger.State n}
    (location : IncidenceLedger.Location n) (he : after.entered = insert location before.entered) :
    creditNodes after = insert location.1 (creditNodes before) := by
  simp only [creditNodes, he, Finset.image_insert]

theorem log_factorial_succ (k : ℕ) :
    Real.log ((k + 1).factorial : ℝ) = Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

/-- Exact credit earned by the next actual admission at a child. -/
theorem factorialCredit_insert {before after : IncidenceLedger.State n}
    (location : IncidenceLedger.Location n) (he : after.entered = insert location before.entered)
    (hnew : location ∉ before.entered) :
    factorialCredit after = factorialCredit before + Real.log (ordinal before location.1 : ℝ) := by
  rw [factorialCredit, creditNodes_insert location he]
  calc
    _ = ∑ identity ∈ insert location.1 (creditNodes before),
        (Real.log ((enteredCount before identity).factorial : ℝ) +
          if identity = location.1 then Real.log (ordinal before location.1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro identity hi
      rw [enteredCount_insert location he hnew]
      by_cases hid : identity = location.1
      · subst identity
        simp only [if_true, ordinal, log_factorial_succ]
        ring
      · simp only [if_neg hid, add_zero]
    _ = (∑ identity ∈ insert location.1 (creditNodes before),
        Real.log ((enteredCount before identity).factorial : ℝ)) +
        Real.log (ordinal before location.1 : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_insert_self, if_true]
    _ = factorialCredit before + Real.log (ordinal before location.1 : ℝ) := by
      congr 1
      by_cases hid : location.1 ∈ creditNodes before
      · rw [Finset.insert_eq_of_mem hid]
        rfl
      · rw [Finset.sum_insert hid, enteredCount_zero_of_not_creditNodes before location.1 hid]
        simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, zero_add]
        rfl

theorem enteredCount_at_pool {ledger : IncidenceLedger.State n} {t : Tree n} {nextIdentity : ℕ}
    (hrep : Represents ledger t) (ha : Allocated t nextIdentity)
    (a : ℕ × Pool n) (hamem : a ∈ storedPools t) : enteredCount ledger a.1 = a.2.members.card := by
  have hf : ledger.entered.filter (fun location => location.1 = a.1) =
      nodeLocations a.1 a.2.members := by
    ext ⟨identity, x⟩
    simp only [Finset.mem_filter, mem_nodeLocations]
    constructor
    · rintro ⟨hl, rfl⟩
      exact ⟨rfl, (treeLocations_at_identity ha a hamem Pool.members x).mp
        (by simpa only [hrep.entered, enteredLocations] using hl)⟩
    · rintro ⟨rfl, hx⟩
      refine ⟨?_, rfl⟩
      rw [hrep.entered]
      exact (treeLocations_at_identity ha a hamem Pool.members x).mpr hx
  rw [enteredCount, hf, nodeLocations_card]

theorem enteredCount_at_fresh {ledger : IncidenceLedger.State n} {t : Tree n} {nextIdentity : ℕ}
    (hrep : Represents ledger t) (ha : Allocated t nextIdentity) : enteredCount ledger nextIdentity = 0 := by
  apply enteredCount_zero_of_not_creditNodes
  intro hmem
  obtain ⟨location, hl, hid⟩ := Finset.mem_image.mp hmem
  have hlt := ha.below location.1 (location_identity_mem Pool.members
    (by simpa only [hrep.entered, enteredLocations] using hl))
  omega

/-- Computed from the actual destination subtree before its admission. -/
def admissionNumber {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) : ℕ :=
  match destinationChild r children with
  | none => 1
  | some a => a.2.pool.members.card + 1

theorem admissionNumber_pos {p : Pool n} {v : Fin n} {c : Fin (p.palette + 1)}
    (r : Promotion.Result p.system p.pins v c) (children : List (ℕ × Tree n)) :
    0 < admissionNumber r children := by
  unfold admissionNumber
  split <;> omega

theorem admissionNumber_le_multiplier {p : Pool n} {children : List (ℕ × Tree n)}
    (h : Parts p children) (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) : admissionNumber r children ≤ birthMultiplier h v hv c r := by
  cases hd : destinationChild r children with
  | none =>
    simpa only [admissionNumber, hd] using Nat.succ_le_of_lt (birthMultiplier_pos h v hv c r)
  | some a =>
    obtain ⟨ha, hkey⟩ := destinationChild_some r children hd
    simpa only [admissionNumber, hd] using birthday_le_multiplier h v hv c r a ha hkey

theorem admissionNumber_eq_ordinal (ledger : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (v : Fin n) (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c)
    (nextIdentity : ℕ) (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity)
    (hrep : Represents ledger (ctx.plug (.node identity p children))) :
    admissionNumber r children = ordinal ledger (receivingIdentity r children nextIdentity) := by
  cases hd : destinationChild r children with
  | none => simp only [admissionNumber, receivingIdentity, hd, ordinal, enteredCount_at_fresh hrep ha, zero_add]
  | some a =>
    obtain ⟨hamem, _⟩ := destinationChild_some r children hd
    have hroot : (rootIdentity a.2, a.2.pool) ∈ storedPools (ctx.plug (.node identity p children)) := by
      apply storedPools_mem_plug ctx
      rw [storedPools]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a, hamem, root_mem_storedPools a.2⟩)
    simp only [admissionNumber, receivingIdentity, hd, ordinal, enteredCount_at_pool hrep ha _ hroot]

theorem promotionLedger_credit (ledger : IncidenceLedger.State n) (ctx : Context n)
    (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n)) (h : Parts p children)
    (v : Fin n) (hv : p.pins v = none) (c : Fin (p.palette + 1))
    (r : Promotion.Result p.system p.pins v c) (nextIdentity : ℕ)
    (ha : Allocated (ctx.plug (.node identity p children)) nextIdentity)
    (hrep : Represents ledger (ctx.plug (.node identity p children))) (kind : IncidenceLedger.Kind) :
    factorialCredit (promotionLedger ledger identity v kind r children nextIdentity) =
      factorialCredit ledger + Real.log (admissionNumber r children : ℝ) := by
  have hnew : (receivingIdentity r children nextIdentity, v) ∉ ledger.entered := by
    rw [hrep.entered]
    exact receivingLocation_not_entered ctx identity p children h v hv c r nextIdentity ha
  have hc := factorialCredit_insert
    (after := promotionLedger ledger identity v kind r children nextIdentity)
    (receivingIdentity r children nextIdentity, v) rfl hnew
  rw [← admissionNumber_eq_ordinal ledger ctx identity p children v c r nextIdentity ha hrep] at hc
  exact hc

end SortingAdversary.Optimal.LedgerBirthCredits
