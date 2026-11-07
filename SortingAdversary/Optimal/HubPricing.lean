import SortingAdversary.Optimal.BatchWindows
import SortingAdversary.Optimal.SignedPrice

/-!
# Connecting actual selected hubs to the signed-price dictionary

The record decoder is arithmetic and executable. It recovers the immutable
batch and aligned block from every actual historical record. Consequently
the dictionary code used by `SignedPrice` can be instantiated by the selected
hub colours, including choices made in batches that have since retired.

The individual probability price follows from the proved palette-window
bound and a pointwise lower bound on the true colour probability. The latter
is exactly the interface supplied by the insertion or calibrated-marginal
lemma; no global signed-price estimate is assumed here.
-/

namespace SortingAdversary.Optimal.HubPricing

open scoped BigOperators
open StableBatches HubSelector BatchWindows DyadicDictionary

/-- Decode the ordinary rows of a dictionary slot. Extra rows are unused
by this theorem; the total code already pays for them. -/
def decodeBlock {M : ℕ} (slot : HubSlot M) : Block :=
  let e := M - slot.1.val
  let row := slot.2.1.val
  let a := e + row
  let packed := slot.2.2.val
  ⟨⟨(packed / 2 ^ row) * 2 ^ a, a⟩, e, packed % 2 ^ row⟩

theorem decode_dictionaryRecord {M births : ℕ} (hcap : births ≤ 2 ^ M)
    (b : Batch) (hb : b ∈ currentBatches births) (e : ℕ) (he : e ≤ b.level)
    (block : Fin (2 ^ (b.level - e))) :
    decodeBlock (dictionaryRecord hcap b hb e he block) = ⟨b, e, block.val⟩ := by
  have heM := he.trans (currentBatches_level_le hcap hb)
  have hrow : e + (b.level - e) = b.level := by omega
  have hdiv : (b.start / b.size * 2 ^ (b.level - e) + block.val) / 2 ^ (b.level - e) =
      b.start / b.size := by
    rw [Nat.mul_comm (b.start / b.size), Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt block.isLt, Nat.add_zero]
  have hmod : (b.start / b.size * 2 ^ (b.level - e) + block.val) % 2 ^ (b.level - e) =
      block.val := by
    rw [Nat.mul_comm (b.start / b.size), Nat.mul_add_mod, Nat.mod_eq_of_lt block.isLt]
  have hstart : b.start / b.size * 2 ^ b.level = b.start :=
    Nat.div_mul_cancel (currentBatches_bounds hb).2
  dsimp [decodeBlock, dictionaryRecord, batchSlot]
  rw [Nat.sub_sub_self heM, hrow, hdiv, hmod, hstart]

/-- A block together with the actual birth-counter state in which it was
available. The state may be earlier than the final dictionary capacity. -/
structure PastBlock (M : ℕ) where
  births : ℕ
  withinCap : births ≤ 2 ^ M
  block : Block
  available : block ∈ allBlocks births

def encode {M : ℕ} (past : PastBlock M) : HubSlot M :=
  dictionaryRecord past.withinCap past.block.batch ((mem_allBlocks _ _).mp past.available).1
    past.block.level ((mem_allBlocks _ _).mp past.available).2.1
    ⟨past.block.index, ((mem_allBlocks _ _).mp past.available).2.2⟩

@[simp] theorem decode_encode {M : ℕ} (past : PastBlock M) : decodeBlock (encode past) = past.block := by
  exact decode_dictionaryRecord _ _ _ _ _ _

@[simp] theorem encode_deficit {M : ℕ} (past : PastBlock M) : (encode past).1.val = M - past.block.level := rfl

@[simp] theorem encode_blockSize {M : ℕ} (past : PastBlock M) : blockSize (encode past) = past.block.size :=
  dictionaryRecord_blockSize _ _ _ _ _ _

/-- Numeric ranks may change while the selected birth identity stays fixed.
This theorem supplies the lifetime consistency of the record decoder. -/
theorem hubColour_stable (oldRank newRank : ℕ → ℕ)
    (hold : Function.Injective oldRank) (hnew : Function.Injective newRank) (block : Block)
    (hpreserve : ∀ a ∈ block.batch.members, ∀ b ∈ block.batch.members,
      oldRank a ≤ oldRank b ↔ newRank a ≤ newRank b) :
    hubColour oldRank hold block = hubColour newRank hnew block := by
  unfold hubColour
  rw [orderedMembers_stable oldRank newRank hold hnew block.batch hpreserve]

/-- A concrete decoder for one node's historical dictionary. -/
def decodeColour {M : ℕ} (rank : ℕ → ℕ) (hinj : Function.Injective rank) (slot : HubSlot M) : ℕ :=
  hubColour rank hinj (decodeBlock slot)

@[simp] theorem decodeColour_encode {M : ℕ} (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    (past : PastBlock M) : decodeColour rank hinj (encode past) = hubColour rank hinj past.block := by
  simp [decodeColour]

/-- The tariff increases with block size. This justifies replacing every
individual block at a destination by the largest one used there. -/
theorem block_tariff_monotone (M : ℕ) :
    Monotone (fun e : ℕ => 2 ^ e * (M - e + 2)) := by
  apply monotone_nat_of_le_succ
  intro e
  by_cases h : e < M
  · have hsub : M - e = M - (e + 1) + 1 := by omega
    rw [hsub, pow_succ]
    nlinarith [Nat.two_pow_pos e, Nat.zero_le (M - (e + 1))]
  · have hsub : M - e = 0 := by omega
    have hsub' : M - (e + 1) = 0 := by omega
    rw [hsub, hsub', pow_succ]
    nlinarith [Nat.two_pow_pos e]

/-- A uniform pointwise probability lower bound on a wide window gives
the actual old-fibre log price of the algorithm's selected hub. -/
theorem selected_log_price_bound {births M lower upper : ℕ}
    (order : Equiv.Perm (Fin births)) {veto : Finset Block} {chosen : Block}
    (hcap : births ≤ 2 ^ M) (hupper : upper ≤ births) (hlarge : 8 ≤ upper - lower)
    (hveto : 4 * vetoCost veto ≤ upper - lower)
    (hchosen : selectWindow order (lower + 1) (upper - 1) veto = some chosen)
    (V probability : ℝ) (hV : 0 < V)
    (hprobability : 1 / (V * (upper - lower : ℕ)) ≤ probability) :
    -Real.log probability ≤
      Real.log ((8 * V) * chosen.size * (M - chosen.level + 2 : ℕ)) := by
  have hwindow := selected_trimmed_window_bound order hcap hupper hlarge hveto hchosen
  have hm : (0 : ℝ) < (upper - lower : ℕ) := by exact_mod_cast (by omega : 0 < upper - lower)
  have hp : 0 < probability := (div_pos (by norm_num) (mul_pos hV hm)).trans_le hprobability
  have hlog := Real.log_le_log (div_pos (by norm_num) (mul_pos hV hm)) hprobability
  rw [Real.log_div (by norm_num) (mul_pos hV hm).ne', Real.log_one, zero_sub] at hlog
  have hcost : V * (upper - lower : ℕ) ≤ (8 * V) * chosen.size * (M - chosen.level + 2 : ℕ) := by
    have hw : ((upper - lower : ℕ) : ℝ) ≤
        8 * (chosen.size : ℝ) * (M - chosen.level + 2 : ℕ) := by exact_mod_cast hwindow
    nlinarith [mul_le_mul_of_nonneg_left hw hV.le]
  have hmono := Real.log_le_log (mul_pos hV hm) hcost
  linarith

/-- Enlarging to the largest block used at this destination preserves the
individual upper price. -/
theorem log_price_le_largest {M : ℕ} (A : ℝ) (hA : 0 < A) (past largest : PastBlock M)
    (hle : past.block.level ≤ largest.block.level) :
    Real.log (A * past.block.size * (M - past.block.level + 2 : ℕ)) ≤
      Real.log (A * largest.block.size * (M - largest.block.level + 2 : ℕ)) := by
  have hsize : (0 : ℝ) < past.block.size := by exact_mod_cast past.block.size_pos
  have hdeficit : (0 : ℝ) < (M - past.block.level + 2 : ℕ) := by
    exact_mod_cast (show 0 < M - past.block.level + 2 by omega)
  apply Real.log_le_log (by positivity)
  have hnat := block_tariff_monotone M hle
  have hreal : (past.block.size : ℝ) * (M - past.block.level + 2 : ℕ) ≤
      (largest.block.size : ℝ) * (M - largest.block.level + 2 : ℕ) := by exact_mod_cast hnat
  nlinarith [mul_le_mul_of_nonneg_left hreal hA.le]

/-! ## Actual finite histories, including all retired batches -/

abbrev GlobalPastBlock {Node : Type*} (exponent : Node → ℕ) := Σ v : Node, PastBlock (exponent v)

def encodeGlobal {Node : Type*} {exponent : Node → ℕ} (past : GlobalPastBlock exponent) : GlobalSlot exponent :=
  ⟨past.1, encode past.2⟩

def destination {Node : Type*} {exponent : Node → ℕ}
    (rank : Node → ℕ → ℕ) (hinj : ∀ v, Function.Injective (rank v))
    (past : GlobalPastBlock exponent) : Node × ℕ :=
  (past.1, hubColour (rank past.1) (hinj past.1) past.2.block)

def decodeGlobalColour {Node : Type*} {exponent : Node → ℕ}
    (rank : Node → ℕ → ℕ) (hinj : ∀ v, Function.Injective (rank v))
    (slot : GlobalSlot exponent) : Node × ℕ :=
  (slot.1, decodeColour (rank slot.1) (hinj slot.1) slot.2)

@[simp] theorem decodeGlobalColour_encode {Node : Type*} {exponent : Node → ℕ}
    (rank : Node → ℕ → ℕ) (hinj : ∀ v, Function.Injective (rank v)) (past : GlobalPastBlock exponent) :
    decodeGlobalColour rank hinj (encodeGlobal past) = destination rank hinj past := by
  rcases past with ⟨v, past⟩
  simp [decodeGlobalColour, encodeGlobal, destination]

section History

variable {Node : Type*} [DecidableEq Node] {exponent : Node → ℕ} {H : ℕ}
variable (rank : Node → ℕ → ℕ) (hinj : ∀ v, Function.Injective (rank v))
variable (events : Fin H → GlobalPastBlock exponent)

def destinations : Finset (Node × ℕ) := Finset.univ.image (fun i => destination rank hinj (events i))

def countAt (c : Node × ℕ) : ℕ :=
  (Finset.univ.filter (fun i => destination rank hinj (events i) = c)).card

/-- This maximum is computed from the actual event history; its selector
does not receive an asserted maximum block as additional data. -/
def largestAt (c : Node × ℕ) : Option (GlobalPastBlock exponent) :=
  List.argmax (fun past => past.2.block.level)
    ((List.ofFn events).filter (fun past => decide (destination rank hinj past = c)))

def largestOr (fallback : GlobalPastBlock exponent) (c : Node × ℕ) : GlobalPastBlock exponent :=
  (largestAt rank hinj events c).getD fallback

theorem largestAt_exists {c : Node × ℕ} (hc : c ∈ destinations rank hinj events) :
    ∃ past, largestAt rank hinj events c = some past := by
  obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
  cases h : largestAt rank hinj events c with
  | some past => exact ⟨past, rfl⟩
  | none =>
      have hempty := List.argmax_eq_none.mp h
      have hmem : events i ∈ (List.ofFn events).filter
          (fun past => decide (destination rank hinj past = c)) := by
        simp [hic, List.mem_ofFn]
      rw [hempty] at hmem
      exact False.elim (List.not_mem_nil hmem)

theorem largestOr_spec (fallback : GlobalPastBlock exponent) {c : Node × ℕ}
    (hc : c ∈ destinations rank hinj events) :
    destination rank hinj (largestOr rank hinj events fallback c) = c ∧
      ∀ i, destination rank hinj (events i) = c →
        (events i).2.block.level ≤ (largestOr rank hinj events fallback c).2.block.level := by
  obtain ⟨past, hpast⟩ := largestAt_exists rank hinj events hc
  have hm : past ∈ largestAt rank hinj events c := by simp [hpast]
  have hmem := List.argmax_mem hm
  have hdest := of_decide_eq_true (List.mem_filter.mp hmem).2
  have hlargest : largestOr rank hinj events fallback c = past := by simp [largestOr, hpast]
  rw [hlargest]
  refine ⟨hdest, ?_⟩
  intro i hi
  apply List.le_of_mem_argmax _ hm
  simp [hi, List.mem_ofFn]

theorem sum_countAt : (∑ c ∈ destinations rank hinj events, countAt rank hinj events c) = H := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin H))) (t := destinations rank hinj events)
    (g := fun i => destination rank hinj (events i))
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun _ => (1 : ℕ))
  simpa [countAt] using h

noncomputable def unitPrice (A : ℝ) (past : GlobalPastBlock exponent) : ℝ :=
  Real.log (A * past.2.block.size * (exponent past.1 - past.2.block.level + 2 : ℕ))

theorem unitPrice_le_largest (A : ℝ) (hA : 0 < A) (fallback : GlobalPastBlock exponent)
    {c : Node × ℕ} (hc : c ∈ destinations rank hinj events) (i : Fin H)
    (hi : destination rank hinj (events i) = c) :
    unitPrice A (events i) ≤ unitPrice A (largestOr rank hinj events fallback c) := by
  have hspec := largestOr_spec rank hinj events fallback hc
  have hnodei : (events i).1 = c.1 := congrArg Prod.fst hi
  have hnodec : (largestOr rank hinj events fallback c).1 = c.1 := congrArg Prod.fst hspec.1
  have hnat := block_tariff_monotone (exponent c.1) (hspec.2 i hi)
  have hreal : ((events i).2.block.size : ℝ) *
      (exponent c.1 - (events i).2.block.level + 2 : ℕ) ≤
      ((largestOr rank hinj events fallback c).2.block.size : ℝ) *
        (exponent c.1 - (largestOr rank hinj events fallback c).2.block.level + 2 : ℕ) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < (events i).2.block.size := by exact_mod_cast (events i).2.block.size_pos
  have hMi := congrArg exponent hnodei
  have hMc := congrArg exponent hnodec
  have hfactorI : exponent (events i).1 - (events i).2.block.level + 2 =
      exponent c.1 - (events i).2.block.level + 2 := by omega
  have hfactorC : exponent (largestOr rank hinj events fallback c).1 -
      (largestOr rank hinj events fallback c).2.block.level + 2 =
      exponent c.1 - (largestOr rank hinj events fallback c).2.block.level + 2 := by omega
  unfold unitPrice
  rw [hfactorI, hfactorC]
  apply Real.log_le_log (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hreal hA.le]

/-- Global signed accounting for an actual finite history of hub records.
Destination counts and largest blocks are computed from the events. The
decoder correctness and subprobability code are derived from those records.

The hypothesis on `countAt` is just the elementary population cap at each
destination. No entropy, code-mass, maximum-block, or signed-price conclusion
is assumed. The factor `A` is absolute for regular pins; scale pins use the
same theorem after their explicit per-pin surcharge is separated.
-/
theorem history_signed_debit_le [Fintype Node] [Nonempty Node]
    (fallback : GlobalPastBlock exponent) (A : ℝ) (hA : 1 ≤ A)
    (hcount : ∀ c ∈ destinations rank hinj events,
      (countAt rank hinj events c : ℝ) ≤ (2 : ℝ) ^ exponent c.1) :
    (∑ i : Fin H, unitPrice A (events i)) -
        (∑ c ∈ destinations rank hinj events, Real.log ((countAt rank hinj events c).factorial : ℝ)) ≤
      SignedPrice.priceCoefficient (Real.exp 1 * A) *
        SignedPrice.entropyEnvelope H
          ((totalCapacity exponent : ℝ) +
            ∑ c ∈ destinations rank hinj events, (countAt rank hinj events c : ℝ) *
              Real.log ((2 : ℝ) ^ exponent c.1 / countAt rank hinj events c)) := by
  let chosen := largestOr rank hinj events fallback
  let selected := fun c => encodeGlobal (chosen c)
  have hApos : 0 < A := by linarith
  have hdecode (c : Node × ℕ) (hc : c ∈ destinations rank hinj events) :
      decodeGlobalColour rank hinj (selected c) = c := by
    rw [show selected c = encodeGlobal (chosen c) by rfl, decodeGlobalColour_encode]
    exact (largestOr_spec rank hinj events fallback hc).1
  have hnode (c : Node × ℕ) (hc : c ∈ destinations rank hinj events) : (chosen c).1 = c.1 :=
    congrArg Prod.fst (largestOr_spec rank hinj events fallback hc).1
  have hcap (c : Node × ℕ) (hc : c ∈ destinations rank hinj events) :
      (countAt rank hinj events c : ℝ) ≤ (2 : ℝ) ^ exponent (selected c).1 := by
    change (countAt rank hinj events c : ℝ) ≤ (2 : ℝ) ^ exponent (chosen c).1
    rw [hnode c hc]
    exact hcount c hc
  have hpriced (c : Node × ℕ) (hc : c ∈ destinations rank hinj events) :
      (∑ i ∈ (Finset.univ : Finset (Fin H)).filter (fun i => destination rank hinj (events i) = c),
        unitPrice A (events i)) - Real.log ((countAt rank hinj events c).factorial : ℝ) ≤
      SignedPrice.factorialDebit A (selected c).2 (countAt rank hinj events c) := by
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin H)).filter (fun i => destination rank hinj (events i) = c))
      (fun i hi =>
      unitPrice_le_largest rank hinj events A hApos fallback hc i (Finset.mem_filter.mp hi).2)
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hrewrite : SignedPrice.factorialDebit A (selected c).2 (countAt rank hinj events c) =
        (countAt rank hinj events c : ℝ) * unitPrice A (chosen c) -
          Real.log ((countAt rank hinj events c).factorial : ℝ) := by
      simp [SignedPrice.factorialDebit, selected, encodeGlobal, unitPrice, Nat.cast_add, Nat.cast_ofNat]
    rw [hrewrite]
    exact sub_le_sub_right hsum _
  have hsum := Finset.sum_le_sum hpriced
  rw [Finset.sum_sub_distrib] at hsum
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin H))) (t := destinations rank hinj events)
    (g := fun i => destination rank hinj (events i))
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun i => unitPrice A (events i))
  rw [hgroup] at hsum
  have hmain := SignedPrice.full_type_signed_debit_le
    (destinations rank hinj events) selected (decodeGlobalColour rank hinj)
    (countAt rank hinj events) A hA hdecode hcap
  have hmass : (∑ c ∈ destinations rank hinj events, (countAt rank hinj events c : ℝ)) = H := by
    exact_mod_cast sum_countAt rank hinj events
  have hentropy :
      (∑ c ∈ destinations rank hinj events, (countAt rank hinj events c : ℝ) *
        Real.log ((2 : ℝ) ^ exponent (selected c).1 / countAt rank hinj events c)) =
      ∑ c ∈ destinations rank hinj events, (countAt rank hinj events c : ℝ) *
        Real.log ((2 : ℝ) ^ exponent c.1 / countAt rank hinj events c) := by
    apply Finset.sum_congr rfl
    intro c hc
    change (countAt rank hinj events c : ℝ) *
        Real.log ((2 : ℝ) ^ exponent (chosen c).1 / countAt rank hinj events c) = _
    rw [hnode c hc]
  rw [hmass, hentropy] at hmain
  exact hsum.trans hmain

end History

end SortingAdversary.Optimal.HubPricing
