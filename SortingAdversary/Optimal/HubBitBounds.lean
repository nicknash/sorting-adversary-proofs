import SortingAdversary.Optimal.HubWork
import Mathlib.Data.Nat.Size

/-!
# Binary operands of the executed dyadic hub routines

Every batch and block used by the measured selectors belongs to their
actual enumeration. Its fields, dyadic powers (including every loop
prefix), endpoint products, midpoint sum, and sorted birth identities fit
the born palette. This also covers the earlier records examined by the
scale-group veto. Threshold counts are bounded independently of the cut.
-/

namespace SortingAdversary.Optimal.HubBitBounds

open PrimitiveWork StableBatches HubSelector

theorem size_le_value (value : ℕ) : Nat.size value ≤ value :=
  Nat.size_le.mpr Nat.lt_two_pow_self

def binaryBound (births : ℕ) : ℕ := 4 * (births + 1) ^ 2

theorem birth_le_binaryBound (births : ℕ) : births + 1 ≤ binaryBound births := by
  unfold binaryBound
  nlinarith

theorem size_of_le {value births : ℕ} (h : value ≤ births + 1) :
    Nat.size value ≤ binaryBound births :=
  (size_le_value value).trans (h.trans (birth_le_binaryBound births))

/-- This includes every intermediate doubling in `powTwo` while the
current-batch reconstruction descends through its binary logarithm. -/
theorem reconstruction_power {births depth e : ℕ}
    (hd : depth ≤ (HubEnumerationWork.logTwo births).value) (he : e ≤ depth) :
    (HubEnumerationWork.powTwo e).value ≤ births + 1 := by
  rw [HubEnumerationWork.powTwo_value]
  rw [HubEnumerationWork.logTwo_value] at hd
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (he.trans hd)).trans (Nat.pow_log_le_add_one 2 births)

/-- The nonempty branch of the prefix decomposition preserves its bounded
integer interval, including the sum formed before the recursive call. -/
theorem prefix_step {births start count size : ℕ}
    (ht : start + count ≤ births) (hs : size ≤ count) :
    start + size ≤ births ∧ count - size ≤ births ∧
      (start + size) + (count - size) ≤ births := by omega

structure BatchOperands (births : ℕ) (batch : Batch) : Prop where
  start : batch.start ≤ births
  level : batch.level ≤ births
  size : batch.size ≤ births
  stop : batch.stop ≤ births
  powers : ∀ e ≤ batch.level, (HubEnumerationWork.powTwo e).value ≤ births

theorem batch_operands {births : ℕ} {batch : Batch}
    (hb : batch ∈ (HubEnumerationWork.current births).value) : BatchOperands births batch := by
  rw [HubEnumerationWork.current_value] at hb
  have hd := HubEnumerationWork.current_batch_bounds hb
  have hs := (currentBatches_bounds hb).1
  refine ⟨?_, hd.1, hd.2, hs, ?_⟩
  · exact (Nat.le_add_right _ _).trans hs
  · intro e he
    rw [HubEnumerationWork.powTwo_value]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) he).trans hd.2

structure BlockOperands (births : ℕ) (block : Block) : Prop where
  batch : BatchOperands births block.batch
  fits : block.Fits
  level : block.level ≤ births
  index : block.index < births
  size : block.size ≤ births
  start : block.start ≤ births
  stop : block.stop ≤ births
  midpoint : block.start + 2 ^ (block.level - 1) ≤ births
  hub : (HubSortWork.hubIndex block).value < births
  indexPower : (HubEnumerationWork.powTwo (block.batch.level - block.level)).value ≤ births
  powers : ∀ e ≤ block.level, (HubEnumerationWork.powTwo e).value ≤ births

theorem block_operands {births : ℕ} {block : Block}
    (hb : block ∈ (HubEnumerationWork.allBlocks births).value) : BlockOperands births block := by
  rw [HubEnumerationWork.allBlocks_value, mem_allBlocks] at hb
  have hbatch := batch_operands (by simpa only [HubEnumerationWork.current_value] using hb.1)
  have hstop : block.stop ≤ births := (block.stop_le_batch_size hb.2).trans hbatch.size
  have hsize : block.size ≤ births := by
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hb.2.1).trans hbatch.size
  have hipower : (HubEnumerationWork.powTwo (block.batch.level - block.level)).value ≤ births :=
    hbatch.powers _ (Nat.sub_le ..)
  have hindex : block.index < births := by
    rw [HubEnumerationWork.powTwo_value] at hipower
    exact hb.2.2.trans_le hipower
  have hmid : block.start + 2 ^ (block.level - 1) ≤ block.stop := by
    have hh : 2 ^ (block.level - 1) ≤ block.size := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    have he : block.stop = block.start + block.size := by unfold Block.stop Block.start; ring
    rw [he]
    exact Nat.add_le_add_left hh _
  refine ⟨hbatch, hb.2, hb.2.1.trans hbatch.level, hindex, hsize,
    block.start_lt_stop.le.trans hstop, hstop, hmid.trans hstop, ?_, hipower, ?_⟩
  · rw [HubSortWork.hubIndex_value]
    exact block.hubIndex_bounds.2.trans_le hstop
  · intro e he
    exact hbatch.powers e (he.trans hb.2.1)

/-- Natural arithmetic fields actually examined by equality, maximum,
admissibility, and midpoint routines. The unreduced midpoint sum is
included, as are the range endpoints and division exponents. -/
def scalars (block : Block) : List ℕ :=
  [block.batch.start, block.batch.level, block.batch.size, block.batch.stop,
    block.level, block.index, block.size, block.start, block.stop,
    (HubSortWork.hubIndex block).value,
    block.level - 1, block.batch.level - block.level,
    (HubEnumerationWork.powTwo (block.batch.level - block.level)).value,
    block.batch.level + 1, block.index + 1, block.start + 2 ^ (block.level - 1)]

theorem scalars_le {births : ℕ} {block : Block} (h : BlockOperands births block)
    {value : ℕ} (hv : value ∈ scalars block) : value ≤ births + 1 := by
  simp only [scalars, List.mem_cons, List.not_mem_nil, or_false] at hv
  have hb := h.batch
  have hlevel := h.level
  have hindex := h.index
  have hsize := h.size
  have hstart := h.start
  have hstop := h.stop
  have hmid := h.midpoint
  have hhub := h.hub
  have hipower := h.indexPower
  rcases hb with ⟨hbs, hbl, hbn, hbt, _⟩
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem scalar_bits {births : ℕ} {block : Block} (h : BlockOperands births block)
    {value : ℕ} (hv : value ∈ scalars block) : Nat.size value ≤ binaryBound births :=
  size_of_le (scalars_le h hv)

theorem block_power_bits {births : ℕ} {block : Block} (h : BlockOperands births block)
    {e : ℕ} (he : e ≤ block.batch.level) :
    Nat.size (HubEnumerationWork.powTwo e).value ≤ binaryBound births :=
  size_of_le ((h.batch.powers e he).trans (Nat.le_succ _))

theorem product_bits {births : ℕ} {block : Block} (h : BlockOperands births block) :
    Nat.size (block.index * (HubEnumerationWork.powTwo block.level).value) ≤ binaryBound births ∧
      Nat.size ((block.index + 1) * (HubEnumerationWork.powTwo block.level).value) ≤ binaryBound births := by
  rw [HubEnumerationWork.powTwo_value]
  exact ⟨size_of_le (h.start.trans (Nat.le_succ _)), size_of_le (h.stop.trans (Nat.le_succ _))⟩

theorem members_lt {births : ℕ} {batch : Batch} (h : BatchOperands births batch)
    {colour : ℕ} (hc : colour ∈ (HubSortWork.members batch).value) : colour < births := by
  rw [HubSortWork.members_value, List.mem_range'] at hc
  obtain ⟨offset, hoffset, rfl⟩ := hc
  simp only [one_mul]
  exact (Nat.add_lt_add_left hoffset _).trans_le h.stop

theorem orderedMembers_lt {births : ℕ} {batch : Batch} (h : BatchOperands births batch)
    (rank : HubSortWork.Rank) {colour : ℕ}
    (hc : colour ∈ (HubSortWork.orderedMembers rank batch).value) : colour < births := by
  simp only [HubSortWork.orderedMembers, HubSortWork.sort_value, List.mem_insertionSort] at hc
  exact members_lt h hc

theorem rank_lt {births : ℕ} (get : Fin births → Result (Fin births)) {colour : ℕ}
    (hc : colour < births) : (HubSortWork.paletteRank get colour).value < births := by
  simp only [HubSortWork.paletteRank, dif_pos hc]
  exact (get ⟨colour, hc⟩).value.isLt

theorem hubColour_lt {births : ℕ} {block : Block} (h : BlockOperands births block)
    (rank : HubSortWork.Rank) : (HubSortWork.hubColour rank block).value < births := by
  have hlen : (HubSortWork.orderedMembers rank block.batch).value.length = block.batch.size := by
    simp only [HubSortWork.orderedMembers, HubSortWork.sort_value, List.length_insertionSort,
      HubSortWork.members_value, List.length_range']
  have hi : (HubSortWork.hubIndex block).value < (HubSortWork.orderedMembers rank block.batch).value.length := by
    rw [hlen, HubSortWork.hubIndex_value]
    exact block.hubIndex_bounds.2.trans_le (block.stop_le_batch_size h.fits)
  simp only [HubSortWork.hubColour, HubSortWork.getD_value]
  rw [List.getD_eq_getElem _ _ hi]
  exact orderedMembers_lt h.batch rank (List.getElem_mem _)

theorem threshold_le {births : ℕ} {batch : Batch} (h : BatchOperands births batch)
    (rank : HubSortWork.Rank) (cut : ℕ) : (HubSortWork.threshold rank cut batch).value ≤ births := by
  rw [HubSortWork.threshold_members]
  exact (Finset.card_filter_le _ _).trans (by simpa only [Batch.card_members] using h.size)

/-- Each recursive suffix of the concrete threshold scan has a bounded
partial count; intermediate additions cannot exceed the batch population. -/
theorem threshold_partial_le {births : ℕ} {batch : Batch} (h : BatchOperands births batch)
    (predicate : ℕ → Result Bool) (xs : List ℕ)
    (hx : xs.Sublist (HubSortWork.members batch).value) :
    (PrimitiveWork.count predicate xs).value ≤ births := by
  rw [PrimitiveWork.count_value]
  apply (List.length_filter_le _ _).trans
  apply hx.length_le.trans
  simpa only [HubSortWork.members_value, List.length_range'] using h.size

theorem selected_operands {births : ℕ} (lo hi : Batch → Result ℕ) (veto : List Block)
    {block : Block} (h : (HubWork.selectBlock births lo hi veto).value = some block) :
    BlockOperands births block := by
  apply block_operands
  rw [HubEnumerationWork.allBlocks_value]
  exact (HubSelector.selected_spec (by simpa only [HubWork.selectBlock_value] using h)).1

theorem group_operands (births : ℕ) (lo hi : ℕ → Batch → Result ℕ) (step count : ℕ)
    (veto : List Block) {block : Block}
    (h : block ∈ (HubWork.selectGroup births lo hi step count veto).value) :
    BlockOperands births block := by
  apply block_operands
  rw [HubEnumerationWork.allBlocks_value]
  rw [HubWork.selectGroup_value] at h
  exact HubSelector.selectGroup_mem_allBlocks _ _ _ _ _ _ h

theorem paletteGroup_operands (births : ℕ) (rank : HubSortWork.Rank)
    (lower upper : ℕ → Result ℕ) (count : ℕ) {block : Block}
    (h : block ∈ (HubWork.selectPaletteGroup births rank lower upper count).value) :
    BlockOperands births block :=
  group_operands births _ _ 0 count [] h

theorem binaryBound_mono {small large : ℕ} (h : small ≤ large) : binaryBound small ≤ binaryBound large := by
  unfold binaryBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)

end SortingAdversary.Optimal.HubBitBounds
