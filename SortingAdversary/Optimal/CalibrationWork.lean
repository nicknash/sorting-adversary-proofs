import SortingAdversary.Optimal.FiniteLoopWork
import SortingAdversary.Optimal.ScaleWalksWork
import SortingAdversary.Optimal.LocalOracle
import SortingAdversary.Optimal.WidthRepair

/-!
# Counted rational first-crossing calibration

The finite searches evaluate their measured CDF callback only at the tested
palette coordinates. The actual smallest crossing is returned, with the
same deterministic endpoint convention as the adversary. Rational comparisons execute explicit signed cross products. The callback's
integer-size certificate supplies the operand width when the bit model is
instantiated.
-/

namespace SortingAdversary.Optimal.CalibrationWork

open PrimitiveWork WidthRepair LocalOracle

variable {n K : ℕ}

def values (q : Fin (K + 1) → Result ℚ) : Fin (K + 1) → ℚ := fun i => (q i).value

/-- Four field reads, two signed integer products, and one comparison. -/
def lessEqual (left right : ℚ) : Result Bool :=
  ⟨decide (left.num * (right.den : ℤ) ≤ right.num * (left.den : ℤ)), 7⟩

@[simp] theorem lessEqual_value (left right : ℚ) :
    (lessEqual left right).value = decide (left ≤ right) := by
  simp only [lessEqual, Rat.le_iff]

def first (q : Fin (K + 1) → Result ℚ) (threshold : ℚ) : Result (Fin (K + 1)) :=
  let found := FiniteLoopWork.scan (fun i =>
    let cdf := q i
    let test := lessEqual threshold cdf.value
    ⟨test.value, cdf.work + test.work⟩)
  ⟨found.value.getD (Fin.last K), found.work + 1⟩

theorem first_value (q : Fin (K + 1) → Result ℚ) (threshold : ℚ)
    (htop : threshold ≤ values q (Fin.last K)) :
    (first q threshold).value = DiscreteCalibration.firstCrossing (values q) threshold htop := by
  have hn : (Finset.univ.filter (fun i : Fin (K + 1) =>
      decide (threshold ≤ (q i).value) = true)).Nonempty :=
    ⟨Fin.last K, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq, values] using htop⟩
  have hset : Finset.univ.filter (fun i : Fin (K + 1) =>
      decide (threshold ≤ (q i).value) = true) = DiscreteCalibration.crossings (values q) threshold := by
    change Finset.univ.filter (fun i : Fin (K + 1) => decide (threshold ≤ (q i).value) = true) =
      Finset.univ.filter (fun i : Fin (K + 1) => threshold ≤ (q i).value)
    apply Finset.filter_congr
    intro i _
    simp only [decide_eq_true_eq]
  have hf := ScaleWalksWork.find_min (fun i : Fin (K + 1) => decide (threshold ≤ (q i).value)) hn
  have hmin : (Finset.univ.filter (fun i : Fin (K + 1) =>
      decide (threshold ≤ (q i).value) = true)).min' hn =
      DiscreteCalibration.firstCrossing (values q) threshold htop := by
    apply le_antisymm
    · apply Finset.min'_le
      rw [hset]
      exact Finset.min'_mem _ _
    · apply Finset.min'_le
      rw [← hset]
      exact Finset.min'_mem _ _
  rw [hmin] at hf
  have hg := congrArg (fun found : Option (Fin (K + 1)) => found.getD (Fin.last K)) hf
  simpa only [first, FiniteLoopWork.scan_value, lessEqual_value, Option.getD_some,
    DiscreteCalibration.firstCrossing] using hg

def firstBound (K cdfWork : ℕ) : ℕ := 3 * (K + 1) + (K + 1) * (cdfWork + 9) + 3

theorem first_work_le (q : Fin (K + 1) → Result ℚ) (threshold : ℚ) (bound : ℕ)
    (h : ∀ i, (q i).work ≤ bound) : (first q threshold).work ≤ firstBound K bound := by
  have hs := FiniteLoopWork.scan_work_le
    (fun i : Fin (K + 1) => (⟨(lessEqual threshold (q i).value).value, (q i).work + 7⟩ : Result Bool))
    (bound + 7) (fun i => Nat.add_le_add_right (h i) 7)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  change (FiniteLoopWork.scan _).work + 1 ≤ _
  unfold firstBound
  dsimp only [lessEqual] at hs ⊢
  omega

def quartiles (q : Fin (K + 1) → Result ℚ) : Result (Fin (K + 1) × Fin (K + 1)) :=
  let lower := first q (1 / 4)
  let upper := first q (3 / 4)
  ⟨(lower.value, upper.value), lower.work + upper.work + 1⟩

theorem quartiles_value (q : Fin (K + 1) → Result ℚ)
    (htop : (3 / 4 : ℚ) ≤ values q (Fin.last K)) :
    (quartiles q).value = DiscreteCalibration.quartiles (values q) htop := by
  have hlow : (1 / 4 : ℚ) ≤ values q (Fin.last K) := le_trans (by norm_num) htop
  simp only [quartiles, first_value q _ hlow, first_value q _ htop, DiscreteCalibration.quartiles]

theorem quartiles_work_le (q : Fin (K + 1) → Result ℚ) (bound : ℕ)
    (h : ∀ i, (q i).work ≤ bound) :
    (quartiles q).work ≤ 2 * firstBound K bound + 1 := by
  have hl := first_work_le q (1 / 4) bound h
  have hu := first_work_le q (3 / 4) bound h
  change (first q (1 / 4)).work + (first q (3 / 4)).work + 1 ≤ _
  omega

def interval {s : State n} (cdf : ℕ → Result ℚ) :
    Result (Fin (s.pool.palette + 1) × Fin (s.pool.palette + 1)) :=
  quartiles (fun i =>
    let answer := cdf (i.val + 1)
    ⟨answer.value, answer.work + 1⟩)

theorem interval_value (s : State n) (H d : ℕ) (g : SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hv : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (cdf : ℕ → Result ℚ)
    (heq : ∀ cut, (cdf cut).value = qCDF s.rows H d R (1 / 16) v cut) :
    (interval (s := s) cdf).value =
      calibrationInterval s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv := by
  let q : Fin (s.pool.palette + 1) → Result ℚ :=
    fun i => let answer := cdf (i.val + 1); ⟨answer.value, answer.work + 1⟩
  have hq : values q = fun i => qCDF s.rows H d R (1 / 16) v (i.val + 1) := by
    funext i
    exact heq (i.val + 1)
  have htop : (3 / 4 : ℚ) ≤ values q (Fin.last s.pool.palette) := by
    rw [hq]
    exact DiscreteCalibration.top_crosses (MarginalCalibration.mass_total s.pool.system v s.pool.count_pos)
      _ (qCDF_sixteenth s.rows s.pool.pin_bounds s.pool.count_pos H d g R hR v hv)
  change (quartiles q).value = _
  rw [quartiles_value q htop]
  simp only [hq, calibrationInterval, MarginalCalibration.selectedInterval]

theorem interval_work_le {s : State n} (cdf : ℕ → Result ℚ) (bound : ℕ)
    (h : ∀ cut, (cdf cut).work ≤ bound) :
    (interval (s := s) cdf).work ≤ 2 * firstBound s.pool.palette (bound + 1) + 1 :=
  quartiles_work_le _ (bound + 1) (fun i => Nat.add_le_add_right (h (i.val + 1)) 1)

end SortingAdversary.Optimal.CalibrationWork

