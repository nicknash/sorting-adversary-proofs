import SortingAdversary.Optimal.HubEnumerationWork
import SortingAdversary.Optimal.BatchWindows
import Mathlib.Data.List.Sort

/-!
# Counted batch sorting and palette-window endpoints

Every palette-rank evaluation supplies its measured cost. A counted insertion
sort computes precisely the unique batch order used by the dyadic selector.
Threshold endpoints can be computed more directly by counting the unsorted
batch members: permutation invariance proves that this is exactly the sorted
prefix count in `BatchWindows.batchThreshold`.
-/

namespace SortingAdversary.Optimal.HubSortWork

open PrimitiveWork StableBatches HubSelector BatchWindows

def orderedInsert (compare : α → α → Result Bool) (a : α) : List α → Result (List α)
  | [] => ⟨[a], 2⟩
  | b :: bs =>
      let test := compare a b
      if test.value then ⟨a :: b :: bs, test.work + 3⟩
      else
        let rest := orderedInsert compare a bs
        ⟨b :: rest.value, test.work + rest.work + 3⟩

@[simp] theorem orderedInsert_value (compare : α → α → Result Bool) (a : α) (xs : List α) :
    (orderedInsert compare a xs).value =
      List.orderedInsert (fun u v => (compare u v).value = true) a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [orderedInsert, List.orderedInsert_cons]; split <;> simp_all

theorem orderedInsert_work_le (compare : α → α → Result Bool) (a : α)
    (xs : List α) (bound : ℕ) (h : ∀ u v, (compare u v).work ≤ bound) :
    (orderedInsert compare a xs).work ≤ xs.length * (bound + 3) + 2 := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons x xs ih =>
      have hx := h a x
      simp only [orderedInsert, List.length_cons, Nat.add_mul, one_mul]
      split <;> dsimp only <;> omega

def sort (compare : α → α → Result Bool) : List α → Result (List α)
  | [] => ⟨[], 1⟩
  | a :: xs =>
      let tail := sort compare xs
      let result := orderedInsert compare a tail.value
      ⟨result.value, tail.work + result.work + 1⟩

@[simp] theorem sort_value (compare : α → α → Result Bool) (xs : List α) :
    (sort compare xs).value =
      List.insertionSort (fun u v => (compare u v).value = true) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sort, orderedInsert_value, ih, List.insertionSort_cons]

theorem sort_work_le (compare : α → α → Result Bool) (xs : List α)
    (bound : ℕ) (h : ∀ u v, (compare u v).work ≤ bound) :
    (sort compare xs).work ≤ (xs.length + 1) ^ 2 * (bound + 4) := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
      have hi := orderedInsert_work_le compare x (sort compare xs).value bound h
      rw [show (sort compare xs).value.length = xs.length by simp only [sort_value, List.length_insertionSort]] at hi
      simp only [sort, List.length_cons]
      nlinarith [Nat.zero_le (xs.length * bound)]

abbrev Rank := ℕ → Result ℕ

def rankValues (rank : Rank) : ℕ → ℕ := fun colour => (rank colour).value

def compareRanks (rank : Rank) (u v : ℕ) : Result Bool :=
  let first := rank u
  let second := rank v
  ⟨decide (first.value ≤ second.value), first.work + second.work + 1⟩

def members (batch : Batch) : Result (List ℕ) :=
  let size := HubEnumerationWork.powTwo batch.level
  ⟨List.range' batch.start size.value, size.work + 3 * size.value + 1⟩

@[simp] theorem members_value (batch : Batch) :
    (members batch).value = List.range' batch.start batch.size := by
  simp only [members, HubEnumerationWork.powTwo_value, Batch.size]

theorem members_work (batch : Batch) :
    (members batch).work = 2 * batch.level + 3 * batch.size + 2 := by
  simp only [members, HubEnumerationWork.powTwo_value, HubEnumerationWork.powTwo_work, Batch.size]
  omega

theorem members_toFinset (batch : Batch) : (members batch).value.toFinset = batch.members := by
  ext colour
  simp [members_value, Batch.members, Batch.stop]

theorem members_nodup (batch : Batch) : (members batch).value.Nodup := by
  rw [members_value]
  exact List.nodup_range'

def orderedMembers (rank : Rank) (batch : Batch) : Result (List ℕ) :=
  let domain := members batch
  let result := sort (compareRanks rank) domain.value
  ⟨result.value, domain.work + result.work⟩

@[simp] theorem orderedMembers_value (rank : Rank) (hinj : Function.Injective (rankValues rank))
    (batch : Batch) :
    (orderedMembers rank batch).value = StableBatches.orderedMembers (rankValues rank) hinj batch := by
  let _ := rankRel_antisymm hinj
  have heq : (fun u v => (compareRanks rank u v).value = true) = rankRel (rankValues rank) := by
    funext u v
    simp [compareRanks, rankValues, rankRel]
  simp only [orderedMembers, sort_value, heq]
  have hp : (List.insertionSort (rankRel (rankValues rank)) (members batch).value).Perm
      (StableBatches.orderedMembers (rankValues rank) hinj batch) := by
    apply (List.perm_insertionSort _ _).trans
    apply (List.perm_ext_iff_of_nodup (members_nodup batch)
      (orderedMembers_nodup _ _ _)).mpr
    intro colour
    rw [mem_orderedMembers]
    rw [← members_toFinset]
    exact List.mem_toFinset.symm
  exact hp.eq_of_pairwise' (List.pairwise_insertionSort _ _)
    (orderedMembers_pairwise _ _ _)

theorem orderedMembers_work_le (rank : Rank) (batch : Batch) (bound : ℕ)
    (h : ∀ colour, (rank colour).work ≤ bound) :
    (orderedMembers rank batch).work ≤
      2 * batch.level + 3 * batch.size + 2 + (batch.size + 1) ^ 2 * (2 * bound + 5) := by
  have hs := sort_work_le (compareRanks rank) (members batch).value (2 * bound + 1) (by
    intro u v
    have hu := h u
    have hv := h v
    dsimp only [compareRanks]
    omega)
  rw [show (members batch).value.length = batch.size by simp only [members_value, List.length_range']] at hs
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  change (members batch).work + _ ≤ _
  rw [members_work]
  omega

def threshold (rank : Rank) (cut : ℕ) (batch : Batch) : Result ℕ :=
  let domain := members batch
  let result := PrimitiveWork.count (fun colour =>
    let position := rank colour
    ⟨decide (position.value < cut), position.work + 1⟩) domain.value
  ⟨result.value, domain.work + result.work⟩

theorem threshold_members (rank : Rank) (cut : ℕ) (batch : Batch) :
    (threshold rank cut batch).value =
      (batch.members.filter (fun colour => rankValues rank colour < cut)).card := by
  simp only [threshold, PrimitiveWork.count_value]
  rw [← List.toFinset_card_of_nodup ((members_nodup batch).filter _)]
  simp only [List.toFinset_filter, decide_eq_true_eq, members_toFinset, rankValues]
  rfl

@[simp] theorem threshold_value (rank : Rank) (hinj : Function.Injective (rankValues rank))
    (cut : ℕ) (batch : Batch) :
    (threshold rank cut batch).value = batchThreshold (rankValues rank) hinj cut batch := by
  rw [threshold_members]
  have hz : batchThreshold (rankValues rank) hinj 0 batch = 0 := by
    simp [batchThreshold, countBelow]
  have hw := batch_window_card (rankValues rank) hinj 0 cut batch
  simpa only [Nat.zero_le, true_and, hz, Nat.sub_zero] using hw

theorem threshold_work_le (rank : Rank) (cut : ℕ) (batch : Batch) (bound : ℕ)
    (h : ∀ colour, (rank colour).work ≤ bound) :
    (threshold rank cut batch).work ≤ 2 * batch.level + batch.size * (bound + 7) + 3 := by
  have hc := PrimitiveWork.count_work_le (fun colour =>
    let position := rank colour
    (⟨decide (position.value < cut), position.work + 1⟩ : Result Bool))
    (members batch).value (bound + 1) (fun colour _ => Nat.add_le_add_right (h colour) 1)
  rw [show (members batch).value.length = batch.size by simp only [members_value, List.length_range']] at hc
  change (members batch).work + _ ≤ _
  rw [members_work]
  calc
    _ ≤ (2 * batch.level + 3 * batch.size + 2) + (batch.size * ((bound + 1) + 3) + 1) := by omega
    _ = _ := by ring

def getD (fallback : α) : List α → ℕ → Result α
  | [], _ => ⟨fallback, 1⟩
  | x :: _, 0 => ⟨x, 1⟩
  | _ :: xs, index + 1 =>
      let rest := getD fallback xs index
      ⟨rest.value, rest.work + 2⟩

@[simp] theorem getD_value (fallback : α) (xs : List α) (index : ℕ) :
    (getD fallback xs index).value = xs.getD index fallback := by
  induction xs generalizing index with
  | nil => rfl
  | cons x xs ih => cases index <;> simp [getD, ih]

theorem getD_work_le (fallback : α) (xs : List α) (index : ℕ) :
    (getD fallback xs index).work ≤ 2 * xs.length + 1 := by
  induction xs generalizing index with
  | nil => simp [getD]
  | cons x xs ih =>
      cases index with
      | zero => simp [getD]
      | succ index => have ht := ih index; simp only [getD, List.length_cons]; omega

def hubIndex (block : Block) : Result ℕ :=
  if block.level = 0 then ⟨block.index, 1⟩
  else
    let size := HubEnumerationWork.powTwo block.level
    let half := HubEnumerationWork.powTwo (block.level - 1)
    ⟨block.index * size.value + half.value - 1, size.work + half.work + 5⟩

@[simp] theorem hubIndex_value (block : Block) : (hubIndex block).value = block.hubIndex := by
  simp only [hubIndex, HubEnumerationWork.powTwo_value, Block.hubIndex, Block.start, Block.size]
  split <;> rfl

theorem hubIndex_work_le (block : Block) : (hubIndex block).work ≤ 4 * block.level + 7 := by
  simp only [hubIndex]
  split
  · dsimp only; omega
  · simp only [HubEnumerationWork.powTwo_work]
    omega

def hubColour (rank : Rank) (block : Block) : Result ℕ :=
  let ordered := orderedMembers rank block.batch
  let index := hubIndex block
  let result := getD 0 ordered.value index.value
  ⟨result.value, ordered.work + index.work + result.work⟩

@[simp] theorem hubColour_value (rank : Rank) (hinj : Function.Injective (rankValues rank))
    (block : Block) :
    (hubColour rank block).value = HubSelector.hubColour (rankValues rank) hinj block := by
  simp only [hubColour, getD_value, orderedMembers_value rank hinj, hubIndex_value,
    HubSelector.hubColour]

theorem hubColour_work_le (rank : Rank) (hinj : Function.Injective (rankValues rank))
    (block : Block) (bound : ℕ) (h : ∀ colour, (rank colour).work ≤ bound) :
    (hubColour rank block).work ≤
      2 * block.batch.level + 4 * block.level + 5 * block.batch.size + 10 +
        (block.batch.size + 1) ^ 2 * (2 * bound + 5) := by
  have hs := orderedMembers_work_le rank block.batch bound h
  have hi := hubIndex_work_le block
  have hg := getD_work_le 0 (orderedMembers rank block.batch).value (hubIndex block).value
  rw [show (orderedMembers rank block.batch).value.length = block.batch.size by
    rw [orderedMembers_value rank hinj, orderedMembers_length]] at hg
  change _ + _ + _ ≤ _
  omega

/-- Measured extension of the finite palette getter; values outside the born
prefix require only the range test. -/
def paletteRank {births : ℕ} (get : Fin births → Result (Fin births)) : Rank := fun colour =>
  if h : colour < births then
    let position := get ⟨colour, h⟩
    ⟨position.value.val, position.work + 1⟩
  else ⟨colour, 1⟩

theorem paletteRank_value {births : ℕ} (order : Equiv.Perm (Fin births))
    (get : Fin births → Result (Fin births)) (heq : ∀ colour, (get colour).value = order colour) :
    rankValues (paletteRank get) = BatchWindows.paletteRank order := by
  funext colour
  simp only [rankValues, paletteRank, BatchWindows.paletteRank]
  split <;> simp only [heq]

theorem paletteRank_work_le {births : ℕ} (get : Fin births → Result (Fin births))
    (bound : ℕ) (h : ∀ colour, (get colour).work ≤ bound) (colour : ℕ) :
    (paletteRank get colour).work ≤ bound + 1 := by
  simp only [paletteRank]
  split
  · exact Nat.add_le_add_right (h _) 1
  · dsimp only; omega

end SortingAdversary.Optimal.HubSortWork
