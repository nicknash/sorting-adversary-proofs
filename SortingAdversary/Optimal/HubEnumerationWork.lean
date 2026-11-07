import SortingAdversary.Optimal.FiniteLoopWork
import SortingAdversary.Optimal.HubSelector

/-!
# Measured reconstruction and enumeration of stable dyadic batches

Powers of two and the binary logarithm below have counted scalar loops.
The nested block enumeration accounts for every generated range, block
record, and list concatenation. Its output has exactly the order used by
`HubSelector.allBlocks`, including the order used to break selection ties.
-/

namespace SortingAdversary.Optimal.HubEnumerationWork

open PrimitiveWork StableBatches HubSelector

def powTwo : ℕ → Result ℕ
  | 0 => ⟨1, 1⟩
  | e + 1 =>
      let previous := powTwo e
      ⟨previous.value * 2, previous.work + 2⟩

@[simp] theorem powTwo_value (e : ℕ) : (powTwo e).value = 2 ^ e := by
  induction e <;> simp_all [powTwo, pow_succ]

theorem powTwo_work (e : ℕ) : (powTwo e).work = 2 * e + 1 := by
  induction e <;> simp_all [powTwo]
  omega

def logTwo (n : ℕ) : Result ℕ :=
  if h : n < 2 then ⟨0, 1⟩
  else
    let previous := logTwo (n / 2)
    ⟨previous.value + 1, previous.work + 3⟩
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

@[simp] theorem logTwo_value (n : ℕ) : (logTwo n).value = Nat.log 2 n := by
  unfold logTwo
  split
  · exact (Nat.log_of_lt ‹n < 2›).symm
  · dsimp only
    rw [logTwo_value (n / 2), Nat.log_div_base]
    have hp : 0 < Nat.log 2 n := Nat.log_pos (by decide) (by omega)
    omega
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem logTwo_work_le (n : ℕ) : (logTwo n).work ≤ 3 * n + 1 := by
  unfold logTwo
  split
  · dsimp only; omega
  · have ih := logTwo_work_le (n / 2)
    have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    dsimp only
    omega
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def prefixWork : ℕ → ℕ → ℕ → Result (List Batch)
  | 0, start, count => ⟨if count = 0 then [] else [⟨start, 0⟩], 2⟩
  | depth + 1, start, count =>
      let size := powTwo (depth + 1)
      if size.value ≤ count then
        let tail := prefixWork depth (start + size.value) (count - size.value)
        ⟨⟨start, depth + 1⟩ :: tail.value, size.work + tail.work + 6⟩
      else
        let tail := prefixWork depth start count
        ⟨tail.value, size.work + tail.work + 6⟩

@[simp] theorem prefix_value (depth start count : ℕ) :
    (prefixWork depth start count).value = prefixBatches depth start count := by
  induction depth generalizing start count with
  | zero => rfl
  | succ depth ih =>
      simp only [prefixWork, powTwo_value, prefixBatches]
      split <;> simp only [ih]

theorem prefix_work_le (depth start count : ℕ) :
    (prefixWork depth start count).work ≤ (depth + 1) * (2 * depth + 10) := by
  induction depth generalizing start count with
  | zero => simp [prefixWork]
  | succ depth ih =>
      simp only [prefixWork, powTwo_value]
      split
      · have ht := ih (start + 2 ^ (depth + 1)) (count - 2 ^ (depth + 1))
        dsimp only
        rw [powTwo_work]
        nlinarith
      · have ht := ih start count
        dsimp only
        rw [powTwo_work]
        nlinarith

def current (births : ℕ) : Result (List Batch) :=
  let depth := logTwo births
  let result := prefixWork depth.value 0 births
  ⟨result.value, depth.work + result.work⟩

@[simp] theorem current_value (births : ℕ) :
    (current births).value = currentBatches births := by
  simp only [current, prefix_value, logTwo_value, currentBatches]

theorem current_work_le (births : ℕ) :
    (current births).work ≤ 3 * births + 1 + (births + 1) * (2 * births + 10) := by
  have hl := logTwo_work_le births
  have hp := prefix_work_le (Nat.log 2 births) 0 births
  have hd := Nat.log_le_self 2 births
  have hm := Nat.mul_le_mul (Nat.add_le_add_right hd 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hd) 10)
  simp only [current, logTwo_value]
  omega

/-- The library range generator uses one successor, one cell construction,
and one loop test per element, plus the final empty test. -/
def range (n : ℕ) : Result (List ℕ) := ⟨List.range n, 3 * n + 1⟩

def atLevel (batch : Batch) (level : ℕ) : Result (List Block) :=
  let size := powTwo (batch.level - level)
  let indices := range size.value
  let result := PrimitiveWork.map (fun j => atom (Block.mk batch level j)) indices.value
  ⟨result.value, size.work + indices.work + result.work + 1⟩

@[simp] theorem atLevel_value (batch : Batch) (level : ℕ) :
    (atLevel batch level).value =
      (List.range (2 ^ (batch.level - level))).map (fun j => Block.mk batch level j) := by
  simp only [atLevel, range, PrimitiveWork.map_value, powTwo_value, atom]

theorem atLevel_length_le (batch : Batch) (level : ℕ) :
    (atLevel batch level).value.length ≤ batch.size := by
  simp only [atLevel_value, List.length_map, List.length_range, Batch.size]
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)

theorem atLevel_work_le (batch : Batch) (level : ℕ) :
    (atLevel batch level).work ≤ 2 * batch.level + 6 * batch.size + 4 := by
  have hm := PrimitiveWork.map_work_le (fun j => atom (Block.mk batch level j))
    (List.range (2 ^ (batch.level - level))) 1 (fun _ _ => le_rfl)
  simp only [List.length_range, Nat.reduceAdd] at hm
  have hs : 2 ^ (batch.level - level) ≤ batch.size :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  simp only [atLevel, range, powTwo_value, powTwo_work]
  omega

def inBatch (batch : Batch) : Result (List Block) :=
  let levels := range (batch.level + 1)
  let result := FiniteLoopWork.flatMap (atLevel batch) levels.value
  ⟨result.value, levels.work + result.work + 1⟩

@[simp] theorem inBatch_value (batch : Batch) :
    (inBatch batch).value = (List.range (batch.level + 1)).flatMap
      (fun level => (List.range (2 ^ (batch.level - level))).map
        (fun j => Block.mk batch level j)) := by
  simp only [inBatch, range, FiniteLoopWork.flatMap_value, atLevel_value]

theorem inBatch_length_le (batch : Batch) :
    (inBatch batch).value.length ≤ (batch.level + 1) * batch.size := by
  simp only [inBatch, range, FiniteLoopWork.flatMap_value, List.length_flatMap]
  have h := List.sum_le_sum (l := List.range (batch.level + 1))
    (f := fun level => (atLevel batch level).value.length)
    (g := fun _ => batch.size) (fun level _ => atLevel_length_le batch level)
  simpa only [List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul] using h

theorem inBatch_work_le (batch : Batch) :
    (inBatch batch).work ≤
      (batch.level + 1) * (2 * batch.level + 8 * batch.size + 9) + 3 := by
  have hf := FiniteLoopWork.flatMap_work_le (atLevel batch) (List.range (batch.level + 1))
    (2 * batch.level + 6 * batch.size + 4) batch.size
    (fun level _ => atLevel_work_le batch level) (fun level _ => atLevel_length_le batch level)
  simp only [List.length_range] at hf
  change (3 * (batch.level + 1) + 1) +
    (FiniteLoopWork.flatMap (atLevel batch) (List.range (batch.level + 1))).work + 1 ≤ _
  calc
    _ ≤ (3 * (batch.level + 1) + 1) +
        ((batch.level + 1) * ((2 * batch.level + 6 * batch.size + 4) + 2 * batch.size + 2) + 1) + 1 := by omega
    _ = _ := by ring

theorem current_batch_bounds {births : ℕ} {batch : Batch}
    (h : batch ∈ currentBatches births) : batch.level ≤ births ∧ batch.size ≤ births := by
  have hd := prefixBatches_level_le (show batch ∈ prefixBatches (Nat.log 2 births) 0 births from h)
  have hs := (currentBatches_bounds h).1
  exact ⟨hd.trans (Nat.log_le_self 2 births), by unfold Batch.stop at hs; omega⟩

def allBlocks (births : ℕ) : Result (List Block) :=
  let batches := current births
  let result := FiniteLoopWork.flatMap inBatch batches.value
  ⟨result.value, batches.work + result.work + 1⟩

@[simp] theorem allBlocks_value (births : ℕ) :
    (allBlocks births).value = HubSelector.allBlocks births := by
  simp only [allBlocks, current_value, FiniteLoopWork.flatMap_value, inBatch_value,
    HubSelector.allBlocks]

theorem allBlocks_length_le (births : ℕ) :
    (allBlocks births).value.length ≤ (births + 1) ^ 3 := by
  have hlen : (currentBatches births).length ≤ births + 1 :=
    (currentBatches_length_le births).trans (Nat.add_le_add_right (Nat.log_le_self 2 births) 1)
  have hsum := List.sum_le_sum (l := currentBatches births)
    (f := fun batch => (inBatch batch).value.length)
    (g := fun _ => (births + 1) * births) (by
      intro batch hb
      obtain ⟨hl, hs⟩ := current_batch_bounds hb
      exact (inBatch_length_le batch).trans
        (Nat.mul_le_mul (Nat.add_le_add_right hl 1) hs))
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul] at hsum
  simp only [allBlocks, current_value, FiniteLoopWork.flatMap_value, List.length_flatMap]
  calc
    _ ≤ (currentBatches births).length * ((births + 1) * births) := hsum
    _ ≤ (births + 1) * ((births + 1) * (births + 1)) :=
      Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ (Nat.le_succ births))
    _ = _ := by ring

def workBound (births : ℕ) : ℕ :=
  3 * births + 1 + (births + 1) * (2 * births + 10) +
    (births + 1) * ((births + 1) * (12 * births + 9) + 5) + 2

theorem allBlocks_work_le (births : ℕ) : (allBlocks births).work ≤ workBound births := by
  have hc := current_work_le births
  have hlen : (currentBatches births).length ≤ births + 1 :=
    (currentBatches_length_le births).trans (Nat.add_le_add_right (Nat.log_le_self 2 births) 1)
  have hf := FiniteLoopWork.flatMap_work_le inBatch (currentBatches births)
    ((births + 1) * (10 * births + 9) + 3) ((births + 1) * births)
    (by
      intro batch hb
      obtain ⟨hl, hs⟩ := current_batch_bounds hb
      apply (inBatch_work_le batch).trans
      exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right hl 1) (by omega)) 3)
    (by
      intro batch hb
      obtain ⟨hl, hs⟩ := current_batch_bounds hb
      exact (inBatch_length_le batch).trans (Nat.mul_le_mul (Nat.add_le_add_right hl 1) hs))
  have hm := Nat.mul_le_mul_right
    (((births + 1) * (10 * births + 9) + 3) + 2 * ((births + 1) * births) + 2) hlen
  have he : ((births + 1) * (10 * births + 9) + 3) + 2 * ((births + 1) * births) + 2 =
      (births + 1) * (12 * births + 9) + 5 := by ring
  rw [he] at hf hm
  simp only [allBlocks, current_value]
  unfold workBound
  omega

theorem workBound_le (births : ℕ) : workBound births ≤ 100 * (births + 1) ^ 3 := by
  unfold workBound
  nlinarith [Nat.zero_le (births ^ 2), Nat.zero_le (births ^ 3)]

end SortingAdversary.Optimal.HubEnumerationWork
