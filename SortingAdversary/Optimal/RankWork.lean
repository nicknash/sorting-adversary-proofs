import SortingAdversary.Optimal.PrimitiveWork
import SortingAdversary.Optimal.ControllerMachine
import Mathlib.Tactic.Ring

/-!
# Measured construction of the frozen ranking

The input row callback reports its own work. We evaluate all predecessor
counts once into a vector, form one vector of distinct keys, and then count
the smaller stored keys for each label. Thus repeated key comparisons do
not repeat predecessor scans. The returned rank vector is exactly the one
used by `ControllerMachine.freeze`.

The counter includes scalar operations, vector access and construction,
finite-list inspection, and both finite index-list constructions. Proofs of
rank bounds and injectivity are erased; they are not executable searches.
-/

namespace SortingAdversary.Optimal.RankWork

open PrimitiveWork

variable {n : ℕ}

abbrev Rows (n : ℕ) := Fin n → Fin n → Result Bool

def values (rows : Rows n) : SparseClosure.Rows (Fin n) :=
  fun u v => (rows u v).value

theorem filter_finRange_length (test : Fin n → Bool) :
    ((List.finRange n).filter test).length =
      (Finset.univ.filter (fun v => test v = true)).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter test)]
  congr 1
  ext v
  simp

/-- The finite label list is constructed once and shared by every column. -/
def predecessors (rows : Rows n) : Result (Vector ℕ n) :=
  let labels := List.finRange n
  let counts := PrimitiveWork.vector (fun v => PrimitiveWork.count (fun u => rows u v) labels)
  ⟨counts.value, counts.work + 3 * n + 1⟩

@[simp] theorem predecessors_value (rows : Rows n) :
    (predecessors rows).value = Vector.ofFn (PublicOrder.predecessorCount (values rows)) := by
  simp only [predecessors, PrimitiveWork.vector_value, PrimitiveWork.count_value]
  apply congrArg Vector.ofFn
  funext v
  exact filter_finRange_length (fun u => (rows u v).value)

theorem predecessors_work_le (rows : Rows n) (bound : ℕ)
    (h : ∀ u v, (rows u v).work ≤ bound) :
    (predecessors rows).work ≤ n * (n * (bound + 3) + 3) + 3 * n + 1 := by
  have hc : ∀ v : Fin n,
      (PrimitiveWork.count (fun u => rows u v) (List.finRange n)).work ≤
        n * (bound + 3) + 1 := by
    intro v
    simpa only [List.length_finRange] using
      PrimitiveWork.count_work_le (fun u => rows u v) (List.finRange n) bound
        (fun u _ => h u v)
  have hv := PrimitiveWork.vector_work_le
    (fun v => PrimitiveWork.count (fun u => rows u v) (List.finRange n))
    (n * (bound + 3) + 1) hc
  simp only [Nat.add_assoc, Nat.reduceAdd] at hv
  change _ + 3 * n + 1 ≤ _
  omega

/-- One stored count read, one multiplication, and one addition per key. -/
def keys (counts : Vector ℕ n) : Result (Vector ℕ n) :=
  PrimitiveWork.vector (fun v => ⟨counts[v] * n + v.val, 3⟩)

@[simp] theorem keys_value (rows : Rows n) :
    (keys (predecessors rows).value).value =
      Vector.ofFn (PublicOrder.extensionKey (values rows)) := by
  simp only [keys, PrimitiveWork.vector_value, predecessors_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  rfl

theorem keys_work_le (counts : Vector ℕ n) : (keys counts).work ≤ n * 5 :=
  PrimitiveWork.vector_work_le _ 3 (fun _ => le_rfl)

/-- Both keys are stored vector reads; their scalar comparison is the third
primitive operation. -/
def smaller (table : Vector ℕ n) (v : Fin n) : Result ℕ :=
  PrimitiveWork.count (fun u => ⟨decide (table[u] < table[v]), 3⟩) (List.finRange n)

@[simp] theorem smaller_value (table : Vector ℕ n) (v : Fin n) :
    (smaller table v).value = (PublicOrder.lowerKeys (fun u => table[u]) v).card := by
  rw [smaller, PrimitiveWork.count_value, filter_finRange_length]
  simp only [decide_eq_true_eq, PublicOrder.lowerKeys]

theorem smaller_work_le (table : Vector ℕ n) (v : Fin n) :
    (smaller table v).work ≤ n * 6 + 1 := by
  simpa only [smaller, List.length_finRange, Nat.reduceAdd] using PrimitiveWork.count_work_le
    (fun u : Fin n => (⟨decide (table[u] < table[v]), 3⟩ : Result Bool))
    (List.finRange n) 3 (fun _ _ => le_rfl)

/-- The source list is shared across all rank scans. `smaller` is used in
the correctness proof; the executable body binds this shared list once. -/
def rankTable (table : Vector ℕ n) : Result (Vector (Fin n) n) :=
  let labels := List.finRange n
  let ranked := PrimitiveWork.vector (fun v =>
    let result := PrimitiveWork.count
      (fun u => ⟨decide (table[u] < table[v]), 3⟩) labels
    ⟨⟨result.value, by
        change (smaller table v).value < n
        rw [smaller_value]
        exact PublicOrder.lowerKeys_card_lt _ _⟩, result.work⟩)
  ⟨ranked.value, ranked.work + 3 * n + 1⟩

theorem rankTable_value (table : Vector ℕ n) :
    (rankTable table).value = Vector.ofFn (fun v =>
      (⟨(PublicOrder.lowerKeys (fun u => table[u]) v).card,
        PublicOrder.lowerKeys_card_lt _ _⟩ : Fin n)) := by
  apply Vector.ext
  intro i hi
  apply Fin.ext
  simp only [rankTable, PrimitiveWork.vector_value, Vector.getElem_ofFn]
  exact smaller_value table ⟨i, hi⟩

theorem rankTable_work_le (table : Vector ℕ n) :
    (rankTable table).work ≤ n * (n * 6 + 3) + 3 * n + 1 := by
  have hv := PrimitiveWork.vector_work_le
    (fun v : Fin n =>
      (⟨(⟨(smaller table v).value,
        by rw [smaller_value]; exact PublicOrder.lowerKeys_card_lt _ _⟩ : Fin n),
        (smaller table v).work⟩ : Result (Fin n)))
    (n * 6 + 1) (fun v => smaller_work_le table v)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hv
  exact Nat.add_le_add_right (Nat.add_le_add_right hv (3 * n)) 1

/-- The three cached passes of the ranking algorithm. -/
def ranks (rows : Rows n) : Result (Vector (Fin n) n) :=
  let counts := predecessors rows
  let keyTable := keys counts.value
  let ranked := rankTable keyTable.value
  ⟨ranked.value, counts.work + keyTable.work + ranked.work⟩

@[simp] theorem ranks_value (rows : Rows n) :
    (ranks rows).value = Vector.ofFn (PublicOrder.extensionRank (values rows)) := by
  simp only [ranks, rankTable_value, keys_value]
  apply Vector.ext
  intro i hi
  apply Fin.ext
  simp [PublicOrder.extensionRank, PublicOrder.lowerKeys]

def workBound (n rowWork : ℕ) : ℕ := n ^ 2 * (rowWork + 9) + 17 * n + 2

theorem ranks_work_le (rows : Rows n) (bound : ℕ)
    (h : ∀ u v, (rows u v).work ≤ bound) :
    (ranks rows).work ≤ workBound n bound := by
  have hp := predecessors_work_le rows bound h
  have hk := keys_work_le (predecessors rows).value
  have hr := rankTable_work_le (keys (predecessors rows).value).value
  change _ + _ + _ ≤ _
  exact (Nat.add_le_add (Nat.add_le_add hp hk) hr).trans_eq (by unfold workBound; ring)

/-- A complete frozen object, with the same ranks and erased injectivity
certificate as the controller's existing freeze operation. -/
def frozen (rows : Rows n) : Result (ControllerMachine.Frozen n) :=
  let result := ranks rows
  ⟨{ ranks := result.value
     injective := by
       change Function.Injective (fun x : Fin n => (ranks rows).value[x])
       simpa only [ranks_value, Fin.getElem_fin, Vector.getElem_ofFn] using
         PublicOrder.extensionRank_injective (values rows) }, result.work⟩

theorem frozen_eq_freeze {p : RecursiveController.Parameters}
    (s : ControllerMachine.Active p n) (rows : Rows n)
    (hrows : values rows = s.tree.pool.system.edge) :
    (frozen rows).value = ControllerMachine.freeze s := by
  simp only [frozen, ranks_value, hrows, ControllerMachine.freeze]

theorem frozen_work_le (rows : Rows n) (bound : ℕ)
    (h : ∀ u v, (rows u v).work ≤ bound) :
    (frozen rows).work ≤ workBound n bound := ranks_work_le rows bound h

/-- A stored Boolean matrix supplies the measured input callback with two
indexed reads. Arbitrary functional row expressions use `ranks_work_le`
with their own measured costs instead. -/
def storedRanks (table : SparseClosure.Table n) : Result (Vector (Fin n) n) :=
  ranks (fun u v => ⟨table[u][v], 2⟩)

@[simp] theorem storedRanks_value (table : SparseClosure.Table n) :
    (storedRanks table).value =
      Vector.ofFn (PublicOrder.extensionRank (SparseClosure.lookup table)) := by
  exact ranks_value _

theorem storedRanks_work_le (table : SparseClosure.Table n) :
    (storedRanks table).work ≤ 11 * n ^ 2 + 17 * n + 2 := by
  exact (ranks_work_le (fun u v => ⟨table[u][v], 2⟩) 2 (fun _ _ => le_rfl)).trans_eq
    (by unfold workBound; ring)

theorem predecessorCount_le (rows : SparseClosure.Rows (Fin n)) (v : Fin n) :
    PublicOrder.predecessorCount rows v ≤ n := by
  simpa only [PublicOrder.predecessorCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun u => rows u v = true) Finset.univ)

/-- Every arithmetic key is smaller than `n²+n`; the counter does not hide
arbitrarily large input integers in key comparisons. -/
theorem extensionKey_lt (rows : SparseClosure.Rows (Fin n)) (v : Fin n) :
    PublicOrder.extensionKey rows v < n ^ 2 + n := by
  have hp := Nat.mul_le_mul_right n (predecessorCount_le rows v)
  change PublicOrder.predecessorCount rows v * n + v.val < _
  calc
    _ ≤ n * n + v.val := Nat.add_le_add_right hp _
    _ < n * n + n := Nat.add_lt_add_left v.isLt _
    _ = n ^ 2 + n := by ring

end SortingAdversary.Optimal.RankWork
