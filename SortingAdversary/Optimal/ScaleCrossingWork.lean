import SortingAdversary.Optimal.FiniteLoopWork
import SortingAdversary.Optimal.ScaleWalksWork
import SortingAdversary.Optimal.ScaleGeometry

/-!
# Counted first crossings along a reconstructed walk

The finite search calls the supplied measured vertex and width getters in
index order. It returns precisely the minimum crossing used by the scale
reservation, including its deterministic choice when several indices cross.
-/

namespace SortingAdversary.Optimal.ScaleCrossingWork

open PrimitiveWork ScaleGeometry

variable {n r : ℕ}

def first (vertex : Fin (r + 1) → Result (Fin n)) (width : Fin n → Result ℕ)
    (threshold : ℕ) : Result (Fin (r + 1)) :=
  let selected := FiniteLoopWork.scan (fun i =>
    let v := vertex i
    let w := width v.value
    ⟨decide (threshold ≤ w.value), v.work + w.work + 1⟩)
  ⟨selected.value.getD (Fin.last r), selected.work + 1⟩

theorem first_value {E : SparseClosure.Rows (Fin n)} (walk : Walk E r) (W : Fin n → ℕ)
    (vertex : Fin (r + 1) → Result (Fin n)) (width : Fin n → Result ℕ)
    (hv : ∀ i, (vertex i).value = walk.vertex i) (hw : ∀ v, (width v).value = W v)
    (threshold : ℕ) (hend : threshold ≤ W walk.finish) :
    (first vertex width threshold).value = walk.firstIndex W threshold hend := by
  have hset : Finset.univ.filter (fun i : Fin (r + 1) =>
      decide (threshold ≤ (width (vertex i).value).value) = true) = walk.crossingIndices W threshold := by
    apply Finset.filter_congr
    intro i _
    simp only [Walk.crossingIndices, decide_eq_true_eq, hv, hw]
  have hn : (Finset.univ.filter (fun i : Fin (r + 1) =>
      decide (threshold ≤ (width (vertex i).value).value) = true)).Nonempty := by
    rw [hset]
    exact walk.crossings_nonempty W threshold hend
  have hf := ScaleWalksWork.find_min
    (fun i : Fin (r + 1) => decide (threshold ≤ (width (vertex i).value).value)) hn
  have hmin : (Finset.univ.filter (fun i : Fin (r + 1) =>
      decide (threshold ≤ (width (vertex i).value).value) = true)).min' hn =
      walk.firstIndex W threshold hend := by
    apply le_antisymm
    · apply Finset.min'_le
      rw [hset]
      exact Finset.min'_mem _ _
    · apply Finset.min'_le
      rw [← hset]
      exact Finset.min'_mem _ _
  rw [hmin] at hf
  have hg := congrArg (fun found : Option (Fin (r + 1)) => found.getD (Fin.last r)) hf
  simpa only [first, FiniteLoopWork.scan_value, Option.getD_some] using hg

def firstBound (length vertexWork widthWork : ℕ) : ℕ :=
  3 * (length + 1) + (length + 1) * (vertexWork + widthWork + 3) + 3

theorem first_work_le (vertex : Fin (r + 1) → Result (Fin n)) (width : Fin n → Result ℕ)
    (threshold vertexWork widthWork : ℕ) (hv : ∀ i, (vertex i).work ≤ vertexWork)
    (hw : ∀ v, (width v).work ≤ widthWork) :
    (first vertex width threshold).work ≤ firstBound r vertexWork widthWork := by
  have hs := FiniteLoopWork.scan_work_le
    (fun i : Fin (r + 1) => (⟨decide (threshold ≤ (width (vertex i).value).value),
      (vertex i).work + (width (vertex i).value).work + 1⟩ : Result Bool))
    (vertexWork + widthWork + 1) (by
      intro i
      have hvi := hv i
      have hwi := hw (vertex i).value
      dsimp only
      omega)
  simpa only [first, firstBound, Nat.add_assoc, Nat.reduceAdd] using Nat.add_le_add_right hs 1

def crossing (vertex : Fin (r + 1) → Result (Fin n)) (width : Fin n → Result ℕ)
    (threshold : ℕ) : Result (Fin n) :=
  let index := first vertex width threshold
  let chosen := vertex index.value
  ⟨chosen.value, index.work + chosen.work + 1⟩

theorem crossing_value {E : SparseClosure.Rows (Fin n)} (walk : Walk E r) (W : Fin n → ℕ)
    (vertex : Fin (r + 1) → Result (Fin n)) (width : Fin n → Result ℕ)
    (hv : ∀ i, (vertex i).value = walk.vertex i) (hw : ∀ v, (width v).value = W v)
    (threshold : ℕ) (hend : threshold ≤ W walk.finish) :
    (crossing vertex width threshold).value = walk.vertex (walk.firstIndex W threshold hend) := by
  simp only [crossing, first_value walk W vertex width hv hw threshold hend, hv]

theorem crossing_work_le (vertex : Fin (r + 1) → Result (Fin n)) (width : Fin n → Result ℕ)
    (threshold vertexWork widthWork : ℕ) (hv : ∀ i, (vertex i).work ≤ vertexWork)
    (hw : ∀ v, (width v).work ≤ widthWork) :
    (crossing vertex width threshold).work ≤ firstBound r vertexWork widthWork + vertexWork + 1 := by
  have hi := first_work_le vertex width threshold vertexWork widthWork hv hw
  have hv' := hv (first vertex width threshold).value
  change _ + _ + 1 ≤ _
  omega

theorem firstBound_mono {length length' vertexWork vertexWork' widthWork : ℕ}
    (hr : length ≤ length') (hv : vertexWork ≤ vertexWork') :
    firstBound length vertexWork widthWork ≤ firstBound length' vertexWork' widthWork := by
  unfold firstBound
  gcongr

end SortingAdversary.Optimal.ScaleCrossingWork
