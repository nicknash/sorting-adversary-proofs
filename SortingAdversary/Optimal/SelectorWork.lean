import SortingAdversary.Optimal.WindowWork
import SortingAdversary.Optimal.WidthScaleSelect

/-!
# Measured finite repair selectors

The selectors retain the adversary's original label and pair order. Their
callbacks expose numerical-width, raw-row, and free-membership lookup costs.
Repeated widths within one candidate pair are cached locally. The value
theorems identify the selected witnesses exactly, including deterministic
ties; no selection is supplied by an existential premise.
-/

namespace SortingAdversary.Optimal.SelectorWork

open PrimitiveWork FiniteLoopWork WidthRepair GraphBalls

variable {n : ℕ}

abbrev Rows (n : ℕ) := Fin n → Fin n → Result Bool

def values (rows : Rows n) := fun x y => (rows x y).value

def neighbor (rows : Rows n) (v u : Fin n) : Result Bool :=
  let outgoing := rows v u
  let incoming := rows u v
  ⟨decide (u ≠ v) && (outgoing.value || incoming.value), outgoing.work + incoming.work + 4⟩

@[simp] theorem neighbor_value (rows : Rows n) (v u : Fin n) :
    (neighbor rows v u).value = decide (u ∈ neighbors (values rows) v) := by
  simp [neighbor, mem_neighbors, values]

theorem neighbor_work_le (rows : Rows n) (v u : Fin n) (row : ℕ)
    (h : ∀ x y, (rows x y).work ≤ row) :
    (neighbor rows v u).work ≤ 2 * row + 4 := by
  have ho := h v u
  have hi := h u v
  change (rows v u).work + (rows u v).work + 4 ≤ _
  omega

def nonisolated (rows : Rows n) (v : Fin n) : Result Bool :=
  let domain := indices n
  let answer := PrimitiveWork.any (neighbor rows v) domain.value
  ⟨answer.value, domain.work + answer.work⟩

@[simp] theorem nonisolated_value (rows : Rows n) (v : Fin n) :
    (nonisolated rows v).value = decide ((neighbors (values rows) v).Nonempty) := by
  apply Bool.eq_iff_iff.mpr
  simp only [nonisolated, indices, PrimitiveWork.any_value, List.any_eq_true, neighbor_value,
    decide_eq_true_eq, List.mem_finRange, true_and]
  rfl

def neighborWorkBound (n row : ℕ) : ℕ := 3 * n + n * (2 * row + 7) + 3

theorem nonisolated_work_le (rows : Rows n) (v : Fin n) (row : ℕ)
    (h : ∀ x y, (rows x y).work ≤ row) :
    (nonisolated rows v).work ≤ neighborWorkBound n row := by
  have ha := PrimitiveWork.any_work_le (neighbor rows v) (List.finRange n) (2 * row + 4)
    (fun u _ => neighbor_work_le rows v u row h)
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at ha
  change (3 * n + 1) + (PrimitiveWork.any (neighbor rows v) (List.finRange n)).work ≤ _
  unfold neighborWorkBound
  have hm : n * (2 * row + 6) ≤ n * (2 * row + 7) := Nat.mul_le_mul_left n (by omega)
  omega

def degree (rows : Rows n) (v : Fin n) : Result ℕ :=
  let domain := indices n
  let answer := PrimitiveWork.count (neighbor rows v) domain.value
  ⟨answer.value, domain.work + answer.work⟩

@[simp] theorem degree_value (rows : Rows n) (v : Fin n) :
    (degree rows v).value = (neighbors (values rows) v).card := by
  simp only [degree, indices, PrimitiveWork.count_value, neighbor_value]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext u
  simp

theorem degree_work_le (rows : Rows n) (v : Fin n) (row : ℕ)
    (h : ∀ x y, (rows x y).work ≤ row) :
    (degree rows v).work ≤ neighborWorkBound n row := by
  have ha := PrimitiveWork.count_work_le (neighbor rows v) (List.finRange n) (2 * row + 4)
    (fun u _ => neighbor_work_le rows v u row h)
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at ha
  change (3 * n + 1) + (PrimitiveWork.count (neighbor rows v) (List.finRange n)).work ≤ _
  unfold neighborWorkBound
  omega

def narrow (rows : Rows n) (widths : Fin n → Result ℕ) (W₀ : ℕ) : Result (Option (Fin n)) :=
  scan (fun v =>
    let incident := nonisolated rows v
    let size := widths v
    ⟨incident.value && decide (size.value < W₀), incident.work + size.work + 2⟩)

theorem narrow_value (s : State n) (rows : Rows n) (widths : Fin n → Result ℕ) (W₀ : ℕ)
    (hr : values rows = s.rows.active) (hw : ∀ v, (widths v).value = s.width v) :
    (narrow rows widths W₀).value = narrowWitness s W₀ := by
  simp only [narrow, scan_value, nonisolated_value, hr, hw, narrowWitness,
    Bool.decide_and]

def narrowWorkBound (n row width : ℕ) : ℕ :=
  3 * n + n * (neighborWorkBound n row + width + 4) + 2

theorem narrow_work_le (rows : Rows n) (widths : Fin n → Result ℕ) (W₀ row width : ℕ)
    (hr : ∀ x y, (rows x y).work ≤ row) (hw : ∀ v, (widths v).work ≤ width) :
    (narrow rows widths W₀).work ≤ narrowWorkBound n row width := by
  apply (scan_work_le _ (neighborWorkBound n row + width + 2) ?_).trans_eq
    (by simp only [narrowWorkBound, Nat.add_assoc, Nat.reduceAdd])
  intro v
  have hi := nonisolated_work_le rows v row hr
  have hs := hw v
  dsimp only
  omega

def steep (rows : Rows n) (widths : Fin n → Result ℕ) (L : ℕ) :
    Result (Option (Fin n × Fin n)) :=
  scanPairs (fun uv =>
    let row := rows uv.1 uv.2
    let left := widths uv.1
    let right := widths uv.2
    ⟨row.value && (decide (L * right.value < left.value) || decide (L * left.value < right.value)),
      row.work + left.work + right.work + 6⟩)

theorem steep_value (s : State n) (rows : Rows n) (widths : Fin n → Result ℕ) (L : ℕ)
    (hr : values rows = s.rows.active) (hw : ∀ v, (widths v).value = s.width v) :
    (steep rows widths L).value = steepWitness s L := by
  have he : ∀ x y, (rows x y).value = s.rows.active x y := fun x y => congrFun (congrFun hr x) y
  simp [steep, scanPairs_value, he, hw, steepWitness, Bool.decide_and, Bool.decide_or]

def steepWorkBound (n row width : ℕ) : ℕ :=
  3 * n + n * (5 * n + 3) + n * n * (row + 2 * width + 8) + 3

theorem steep_work_le (rows : Rows n) (widths : Fin n → Result ℕ) (L row width : ℕ)
    (hr : ∀ x y, (rows x y).work ≤ row) (hw : ∀ v, (widths v).work ≤ width) :
    (steep rows widths L).work ≤ steepWorkBound n row width := by
  apply (scanPairs_work_le _ (row + 2 * width + 6) ?_).trans_eq
    (by simp only [steepWorkBound, Nat.add_assoc, Nat.reduceAdd])
  intro uv
  have he := hr uv.1 uv.2
  have hl := hw uv.1
  have hr := hw uv.2
  dsimp only
  omega

def largeDegree (rows : Rows n) (free : Fin n → Result Bool) (D : ℕ) : Result (Option (Fin n)) :=
  scan (fun v =>
    let hf := free v
    let hd := degree rows v
    ⟨hf.value && decide (D ≤ hd.value), hf.work + hd.work + 2⟩)

theorem largeDegree_value (rows : Rows n) (free : Fin n → Result Bool) (F : Finset (Fin n))
    (D : ℕ) (hf : ∀ v, (free v).value = decide (v ∈ F)) :
    (largeDegree rows free D).value = SparseRepairGraph.degreeWitness (values rows) F D := by
  simp only [largeDegree, scan_value, hf, degree_value, SparseRepairGraph.degreeWitness,
    Bool.decide_and]

def degreeWorkBound (n row free : ℕ) : ℕ :=
  3 * n + n * (free + neighborWorkBound n row + 4) + 2

theorem largeDegree_work_le (rows : Rows n) (free : Fin n → Result Bool) (D row freeWork : ℕ)
    (hr : ∀ x y, (rows x y).work ≤ row) (hf : ∀ v, (free v).work ≤ freeWork) :
    (largeDegree rows free D).work ≤ degreeWorkBound n row freeWork := by
  apply (scan_work_le _ (freeWork + neighborWorkBound n row + 2) ?_).trans_eq
    (by simp only [degreeWorkBound, Nat.add_assoc, Nat.reduceAdd])
  intro v
  have hd := degree_work_le rows v row hr
  have hm := hf v
  dsimp only
  omega

end SortingAdversary.Optimal.SelectorWork
