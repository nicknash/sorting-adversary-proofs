import SortingAdversary.Optimal.HubSortWork
import SortingAdversary.Optimal.ScaleHubs

/-!
# Primitive work of the actual hub and scale-group selectors

The veto is an explicit list of earlier block records. Membership scans this
list, and adding a selected record is one cons operation. Its finite-set
interpretation gives exactly the original selector, including deterministic
ties. Window callbacks and palette getters report their measured evaluation
costs; no nested function is treated as a free lookup.
-/

namespace SortingAdversary.Optimal.HubWork

open PrimitiveWork StableBatches HubSelector HubSortWork

def blockEqual (a b : Block) : Result Bool :=
  ⟨decide (a = b), 15⟩

def vetoed (veto : List Block) (block : Block) : Result Bool :=
  PrimitiveWork.any (blockEqual block) veto

@[simp] theorem vetoed_value (veto : List Block) (block : Block) :
    (vetoed veto block).value = decide (block ∈ veto.toFinset) := by
  apply Bool.eq_iff_iff.mpr
  simp only [vetoed, PrimitiveWork.any_value, blockEqual, List.any_eq_true,
    decide_eq_true_eq, List.mem_toFinset]
  constructor
  · rintro ⟨other, hother, heq⟩
    simpa only [← heq] using hother
  · intro h
    exact ⟨block, h, rfl⟩

theorem vetoed_work_le (veto : List Block) (block : Block) :
    (vetoed veto block).work ≤ 17 * veto.length + 2 := by
  simpa only [vetoed, Nat.mul_comm, Nat.reduceAdd] using
    PrimitiveWork.any_work_le (blockEqual block) veto 15 (fun _ _ => le_rfl)

def admissible (lo hi : Batch → Result ℕ) (veto : List Block) (block : Block) : Result Bool :=
  let lower := lo block.batch
  let upper := hi block.batch
  let size := HubEnumerationWork.powTwo block.level
  let forbidden := vetoed veto block
  ⟨decide (lower.value ≤ block.index * size.value ∧
      (block.index + 1) * size.value ≤ upper.value) && !forbidden.value,
    lower.work + upper.work + size.work + forbidden.work + 8⟩

@[simp] theorem admissible_value (lo hi : Batch → Result ℕ) (veto : List Block) (block : Block) :
    (admissible lo hi veto block).value = decide
      (HubSelector.admissible (fun b => (lo b).value) (fun b => (hi b).value) veto.toFinset block) := by
  simp [admissible, HubSelector.admissible, InWindow, Block.start, Block.stop, Block.size]

theorem admissible_work_le (births : ℕ) (lo hi : Batch → Result ℕ) (veto : List Block)
    (bound : ℕ) (hlo : ∀ b ∈ currentBatches births, (lo b).work ≤ bound)
    (hhi : ∀ b ∈ currentBatches births, (hi b).work ≤ bound)
    (block : Block) (hb : block ∈ HubSelector.allBlocks births) :
    (admissible lo hi veto block).work ≤ 2 * bound + 2 * births + 17 * veto.length + 11 := by
  obtain ⟨hbatch, hfits⟩ := (mem_allBlocks births block).mp hb
  have hl := hlo block.batch hbatch
  have hu := hhi block.batch hbatch
  have hv := vetoed_work_le veto block
  have hd := hfits.1.trans (HubEnumerationWork.current_batch_bounds hbatch).1
  simp only [admissible, HubEnumerationWork.powTwo_work]
  omega

def maximum (blocks : List Block) : Result (Option Block) :=
  FiniteLoopWork.foldl (fun current block =>
    match current with
    | none => ⟨some block, 1⟩
    | some old => ⟨if old.level < block.level then some block else some old, 4⟩)
    none blocks

@[simp] theorem maximum_value (blocks : List Block) :
    (maximum blocks).value = List.argmax Block.level blocks := by
  simp only [maximum, FiniteLoopWork.foldl_value, List.argmax]
  apply congrArg (fun f => blocks.foldl f none)
  funext current block
  cases current <;> rfl

theorem maximum_work_le (blocks : List Block) :
    (maximum blocks).work ≤ blocks.length * 5 + 1 := by
  apply FiniteLoopWork.foldl_work_le _ _ _ 4
  intro current block _
  cases current <;> dsimp only <;> omega

def selectBlock (births : ℕ) (lo hi : Batch → Result ℕ) (veto : List Block) : Result (Option Block) :=
  let blocks := HubEnumerationWork.allBlocks births
  let candidates := FiniteLoopWork.filter (admissible lo hi veto) blocks.value
  let result := maximum candidates.value
  ⟨result.value, blocks.work + candidates.work + result.work⟩

@[simp] theorem selectBlock_value (births : ℕ) (lo hi : Batch → Result ℕ) (veto : List Block) :
    (selectBlock births lo hi veto).value = HubSelector.selectBlock births
      (fun b => (lo b).value) (fun b => (hi b).value) veto.toFinset := by
  simp only [selectBlock, maximum_value, FiniteLoopWork.filter_value,
    HubEnumerationWork.allBlocks_value, admissible_value, HubSelector.selectBlock]

def selectionBound (births windowWork vetoLength : ℕ) : ℕ :=
  HubEnumerationWork.workBound births +
    (births + 1) ^ 3 * (2 * windowWork + 2 * births + 17 * vetoLength + 19) + 2

theorem selectionBound_mono (births windowWork : ℕ) {small large : ℕ} (h : small ≤ large) :
    selectionBound births windowWork small ≤ selectionBound births windowWork large := by
  unfold selectionBound
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (by omega)) _) 2

theorem selectBlock_work_le (births : ℕ) (lo hi : Batch → Result ℕ) (veto : List Block)
    (bound : ℕ) (hlo : ∀ b ∈ currentBatches births, (lo b).work ≤ bound)
    (hhi : ∀ b ∈ currentBatches births, (hi b).work ≤ bound) :
    (selectBlock births lo hi veto).work ≤ selectionBound births bound veto.length := by
  have he := HubEnumerationWork.allBlocks_work_le births
  have hn := HubEnumerationWork.allBlocks_length_le births
  have hf := FiniteLoopWork.filter_work_le (admissible lo hi veto)
    (HubEnumerationWork.allBlocks births).value
    (2 * bound + 2 * births + 17 * veto.length + 11)
    (fun block hb => admissible_work_le births lo hi veto bound hlo hhi block
      (by simpa only [HubEnumerationWork.allBlocks_value] using hb))
  have hm := maximum_work_le
    (FiniteLoopWork.filter (admissible lo hi veto) (HubEnumerationWork.allBlocks births).value).value
  have hfilter :
      (FiniteLoopWork.filter (admissible lo hi veto) (HubEnumerationWork.allBlocks births).value).value.length ≤
        (HubEnumerationWork.allBlocks births).value.length := by
    rw [FiniteLoopWork.filter_value]
    exact List.length_filter_le _ _
  have hmax := hm.trans (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hfilter) 1)
  change _ + _ + _ ≤ _
  unfold selectionBound
  have hs :
      (HubEnumerationWork.allBlocks births).value.length *
        ((2 * bound + 2 * births + 17 * veto.length + 11) + 3) +
      (HubEnumerationWork.allBlocks births).value.length * 5 =
      (HubEnumerationWork.allBlocks births).value.length *
        (2 * bound + 2 * births + 17 * veto.length + 19) := by ring
  have hlarge := Nat.mul_le_mul_right
    (2 * bound + 2 * births + 17 * veto.length + 19) hn
  omega

def thresholdBound (births rankWork : ℕ) : ℕ := 2 * births + births * (rankWork + 7) + 3

theorem threshold_current_work_le (rank : Rank) (births cut : ℕ) (bound : ℕ)
    (h : ∀ colour, (rank colour).work ≤ bound) (batch : Batch)
    (hb : batch ∈ currentBatches births) :
    (threshold rank cut batch).work ≤ thresholdBound births bound := by
  have ht := threshold_work_le rank cut batch bound h
  obtain ⟨hl, hs⟩ := HubEnumerationWork.current_batch_bounds hb
  exact ht.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 2 hl) (Nat.mul_le_mul_right _ hs)) 3)

def selectWindow (births : ℕ) (rank : Rank) (lower upper : ℕ) (veto : List Block) : Result (Option Block) :=
  selectBlock births (threshold rank lower) (threshold rank upper) veto

theorem selectWindow_value {births : ℕ} (order : Equiv.Perm (Fin births))
    (rank : Rank) (hrank : rankValues rank = BatchWindows.paletteRank order)
    (lower upper : ℕ) (veto : List Block) :
    (selectWindow births rank lower upper veto).value =
      BatchWindows.selectWindow order lower upper veto.toFinset := by
  have hinj : Function.Injective (rankValues rank) := by
    rw [hrank]
    exact BatchWindows.paletteRank_injective order
  simp only [selectWindow, selectBlock_value, threshold_value rank hinj]
  simp only [hrank, BatchWindows.selectWindow]

theorem selectWindow_work_le (births : ℕ) (rank : Rank) (lower upper : ℕ) (veto : List Block)
    (bound : ℕ) (h : ∀ colour, (rank colour).work ≤ bound) :
    (selectWindow births rank lower upper veto).work ≤
      selectionBound births (thresholdBound births bound) veto.length :=
  selectBlock_work_le births _ _ veto _
    (fun b hb => threshold_current_work_le rank births lower bound h b hb)
    (fun b hb => threshold_current_work_le rank births upper bound h b hb)

def selectGroup (births : ℕ) (lo hi : ℕ → Batch → Result ℕ) :
    ℕ → ℕ → List Block → Result (List Block)
  | _, 0, _ => ⟨[], 1⟩
  | step, count + 1, veto =>
      let selected := selectBlock births (lo step) (hi step) veto
      match selected.value with
      | none => ⟨[], selected.work + 1⟩
      | some block =>
          let tail := selectGroup births lo hi (step + 1) count (block :: veto)
          ⟨block :: tail.value, selected.work + tail.work + 2⟩

@[simp] theorem selectGroup_value (births : ℕ) (lo hi : ℕ → Batch → Result ℕ)
    (step count : ℕ) (veto : List Block) :
    (selectGroup births lo hi step count veto).value =
      HubSelector.selectGroup births (fun j b => (lo j b).value) (fun j b => (hi j b).value)
        step count veto.toFinset := by
  induction count generalizing step veto with
  | zero => rfl
  | succ count ih =>
      simp only [selectGroup, selectBlock_value, HubSelector.selectGroup]
      split <;> simp_all only [List.toFinset_cons]

theorem selectGroup_work_le (births : ℕ) (lo hi : ℕ → Batch → Result ℕ)
    (step count : ℕ) (veto : List Block) (bound : ℕ)
    (hlo : ∀ j b, b ∈ currentBatches births → (lo j b).work ≤ bound)
    (hhi : ∀ j b, b ∈ currentBatches births → (hi j b).work ≤ bound) :
    (selectGroup births lo hi step count veto).work ≤
      count * (selectionBound births bound (veto.length + count) + 2) + 1 := by
  induction count generalizing step veto with
  | zero => simp [selectGroup]
  | succ count ih =>
      have hs := (selectBlock_work_le births (lo step) (hi step) veto bound (hlo step) (hhi step)).trans
        (selectionBound_mono births bound (Nat.le_add_right veto.length (count + 1)))
      simp only [selectGroup]
      split
      · dsimp only
        have hm : selectionBound births bound (veto.length + (count + 1)) + 2 ≤
            (count + 1) * (selectionBound births bound (veto.length + (count + 1)) + 2) :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos count)
        omega
      · rename_i block hblock
        have ht := ih (step + 1) (block :: veto)
        simp only [List.length_cons] at ht
        have he : veto.length + 1 + count = veto.length + (count + 1) := by omega
        rw [he] at ht
        dsimp only
        simp only [Nat.add_mul, one_mul]
        omega

def lowerThreshold (rank : Rank) (lower : ℕ → Result ℕ) (j : ℕ) (batch : Batch) : Result ℕ :=
  let cut := lower j
  let result := threshold rank (cut.value + 1) batch
  ⟨result.value, cut.work + result.work + 1⟩

def upperThreshold (rank : Rank) (upper : ℕ → Result ℕ) (j : ℕ) (batch : Batch) : Result ℕ :=
  let cut := upper j
  let result := threshold rank (cut.value - 1) batch
  ⟨result.value, cut.work + result.work + 1⟩

def selectPaletteGroup (births : ℕ) (rank : Rank) (lower upper : ℕ → Result ℕ)
    (count : ℕ) : Result (List Block) :=
  selectGroup births (lowerThreshold rank lower) (upperThreshold rank upper) 0 count []

theorem selectPaletteGroup_value {births : ℕ} (order : Equiv.Perm (Fin births))
    (rank : Rank) (hrank : rankValues rank = BatchWindows.paletteRank order)
    (lower upper : ℕ → Result ℕ) (count : ℕ) :
    (selectPaletteGroup births rank lower upper count).value =
      ScaleHubs.selectPaletteGroup order (fun j => (lower j).value) (fun j => (upper j).value) count := by
  have hinj : Function.Injective (rankValues rank) := by
    rw [hrank]
    exact BatchWindows.paletteRank_injective order
  simp only [selectPaletteGroup, selectGroup_value, lowerThreshold, upperThreshold,
    threshold_value rank hinj, List.toFinset_nil, ScaleHubs.selectPaletteGroup]
  simp only [hrank]

theorem selectPaletteGroup_work_le (births : ℕ) (rank : Rank) (lower upper : ℕ → Result ℕ)
    (count rankWork cutWork : ℕ) (hrank : ∀ colour, (rank colour).work ≤ rankWork)
    (hlower : ∀ j, (lower j).work ≤ cutWork) (hupper : ∀ j, (upper j).work ≤ cutWork) :
    (selectPaletteGroup births rank lower upper count).work ≤
      count * (selectionBound births (cutWork + thresholdBound births rankWork + 1) count + 2) + 1 := by
  have h := selectGroup_work_le births (lowerThreshold rank lower) (upperThreshold rank upper)
    0 count [] (cutWork + thresholdBound births rankWork + 1)
    (by
      intro j batch hb
      exact Nat.add_le_add_right (Nat.add_le_add (hlower j)
        (threshold_current_work_le rank births ((lower j).value + 1) rankWork hrank batch hb)) 1)
    (by
      intro j batch hb
      exact Nat.add_le_add_right (Nat.add_le_add (hupper j)
        (threshold_current_work_le rank births ((upper j).value - 1) rankWork hrank batch hb)) 1)
  simpa only [selectPaletteGroup, List.length_nil, Nat.zero_add] using h

theorem selectionBound_le (births windowWork vetoLength : ℕ) :
    selectionBound births windowWork vetoLength ≤
      (births + 1) ^ 3 * (2 * windowWork + 2 * births + 17 * vetoLength + 121) := by
  have he := HubEnumerationWork.workBound_le births
  have hp : 1 ≤ (births + 1) ^ 3 := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos births))
  unfold selectionBound
  nlinarith

def windowPolynomial (births rankWork vetoLength : ℕ) : ℕ :=
  (births + 1) ^ 4 * (2 * rankWork + 17 * vetoLength + 150)

theorem windowPolynomial_bound (births rankWork vetoLength : ℕ) :
    selectionBound births (thresholdBound births rankWork) vetoLength ≤
      windowPolynomial births rankWork vetoLength := by
  apply (selectionBound_le _ _ _).trans
  have hi : 2 * thresholdBound births rankWork + 2 * births + 17 * vetoLength + 121 ≤
      (births + 1) * (2 * rankWork + 17 * vetoLength + 150) := by
    unfold thresholdBound
    nlinarith [Nat.zero_le (births * vetoLength)]
  exact (Nat.mul_le_mul_left ((births + 1) ^ 3) hi).trans_eq (by unfold windowPolynomial; ring)

theorem selectWindow_polynomial (births : ℕ) (rank : Rank) (lower upper : ℕ) (veto : List Block)
    (bound : ℕ) (h : ∀ colour, (rank colour).work ≤ bound) :
    (selectWindow births rank lower upper veto).work ≤ windowPolynomial births bound veto.length :=
  (selectWindow_work_le births rank lower upper veto bound h).trans (windowPolynomial_bound ..)

def groupPolynomial (births count rankWork cutWork : ℕ) : ℕ :=
  count * ((births + 1) ^ 4 * (2 * rankWork + 2 * cutWork + 17 * count + 160) + 2) + 1

theorem selectPaletteGroup_polynomial (births : ℕ) (rank : Rank) (lower upper : ℕ → Result ℕ)
    (count rankWork cutWork : ℕ) (hrank : ∀ colour, (rank colour).work ≤ rankWork)
    (hlower : ∀ j, (lower j).work ≤ cutWork) (hupper : ∀ j, (upper j).work ≤ cutWork) :
    (selectPaletteGroup births rank lower upper count).work ≤ groupPolynomial births count rankWork cutWork := by
  have hs := selectionBound_le births (cutWork + thresholdBound births rankWork + 1) count
  have hi : 2 * (cutWork + thresholdBound births rankWork + 1) + 2 * births + 17 * count + 121 ≤
      (births + 1) * (2 * rankWork + 2 * cutWork + 17 * count + 160) := by
    unfold thresholdBound
    nlinarith [Nat.zero_le (births * count), Nat.zero_le (births * cutWork)]
  have ht := hs.trans (Nat.mul_le_mul_left ((births + 1) ^ 3) hi)
  have he : (births + 1) ^ 3 *
      ((births + 1) * (2 * rankWork + 2 * cutWork + 17 * count + 160)) =
      (births + 1) ^ 4 * (2 * rankWork + 2 * cutWork + 17 * count + 160) := by ring
  rw [he] at ht
  exact (selectPaletteGroup_work_le births rank lower upper count rankWork cutWork hrank hlower hupper).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left count (Nat.add_le_add_right ht 2)) 1)

/-- Every record chosen by the real selector lies in the bounded current
dictionary. This discharges the size parameters of the counted hub sort. -/
theorem current_hub_work_le (births : ℕ) (rank : Rank)
    (hinj : Function.Injective (rankValues rank)) (block : Block)
    (hb : block ∈ HubSelector.allBlocks births) (bound : ℕ)
    (h : ∀ colour, (rank colour).work ≤ bound) :
    (HubSortWork.hubColour rank block).work ≤
      11 * births + 10 + (births + 1) ^ 2 * (2 * bound + 5) := by
  obtain ⟨hbatch, hfits⟩ := (mem_allBlocks births block).mp hb
  obtain ⟨hl, hs⟩ := HubEnumerationWork.current_batch_bounds hbatch
  have hbLevel := hfits.1.trans hl
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2
  have hm := Nat.mul_le_mul_right (2 * bound + 5) hpow
  have hc := HubSortWork.hubColour_work_le rank hinj block bound h
  omega

theorem current_block_fields (births : ℕ) (block : Block)
    (hb : block ∈ HubSelector.allBlocks births) :
    block.batch.start < births ∧ block.batch.level ≤ Nat.log 2 births ∧
      block.level ≤ Nat.log 2 births ∧ block.index < births ∧
      block.size ≤ births ∧ block.hubIndex < births := by
  obtain ⟨hbatch, hfits⟩ := (mem_allBlocks births block).mp hb
  have hstop := (currentBatches_bounds hbatch).1
  have hsize := (HubEnumerationWork.current_batch_bounds hbatch).2
  have hlevel := prefixBatches_level_le
    (show block.batch ∈ prefixBatches (Nat.log 2 births) 0 births from hbatch)
  have hindex : 2 ^ (block.batch.level - block.level) ≤ block.batch.size :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  refine ⟨?_, hlevel, hfits.1.trans hlevel, hfits.2.trans_le (hindex.trans hsize), ?_, ?_⟩
  · have hpositive := block.batch.size_pos
    unfold Batch.stop at hstop
    omega
  · exact (Nat.pow_le_pow_right (by decide) hfits.1).trans hsize
  · exact block.hubIndex_bounds.2.trans_le ((Block.stop_le_batch_size hfits).trans hsize)

end SortingAdversary.Optimal.HubWork
