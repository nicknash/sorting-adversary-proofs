import SortingAdversary.Optimal.ClockContraction

/-!
# Explicit rational and integer choices for the local oracle

Every constant here is computed by integer arithmetic, rational arithmetic and
natural ceilings. Logarithmic upper roundings are conservatively replaced by
`r ≤ 2^ceil(r)`. These larger constants are independent of the input size and
suffice for the same local accuracy and eventual uniform-stage selection.
-/

namespace SortingAdversary.Optimal.LocalParameters

/-- Denominator of the small-clock cutoff. -/
def clockScale (M : ℕ) : ℕ := 8 * M ^ 2

/-- Small-clock cutoff used in the finite union bound. -/
def clockThreshold (M : ℕ) : ℚ := 1 / clockScale M

/-- An integer high moment satisfying the required contraction inequality. -/
def momentOrder (H M : ℕ) : ℕ := 8 * M * clockScale M ^ H

/-- The insertion loss with the manuscript's bound of `2M` comparables. -/
def insertionConstant (M : ℕ) : ℕ := 2 * 4 ^ (2 * M)

/-- Relative discrepancy scale. -/
def relativeTolerance (M : ℕ) (ε : ℚ) : ℚ := ε / (16 * insertionConstant M)

/-- Fully explicit conservative replacement for the two logarithmic upper
roundings in the manuscript. -/
def sweepCount (H M : ℕ) (R ε : ℚ) : ℕ :=
  momentOrder H M * ⌈2 * R / relativeTolerance M ε⌉₊ + ⌈8 / ε⌉₊

/-- An integer width threshold sufficient for both the additive sweep errors
and the insertion near-tie term. -/
def minimumWidth (H M : ℕ) (R ε : ℚ) : ℕ :=
  ⌈max (2 * (H : ℚ) * sweepCount H M R ε / relativeTolerance M ε)
    (4 * (insertionConstant M : ℚ) / ε)⌉₊ + 1

theorem clockScale_pos {M : ℕ} (hM : 0 < M) : 0 < clockScale M := by
  unfold clockScale
  positivity

theorem momentOrder_pos {M : ℕ} (H : ℕ) (hM : 0 < M) : 0 < momentOrder H M := by
  unfold momentOrder
  have := clockScale_pos hM
  positivity

theorem clockThreshold_bounds {M : ℕ} (hM : 0 < M) :
    0 ≤ clockThreshold M ∧ clockThreshold M ≤ 1 := by
  have hscale : (1 : ℚ) ≤ clockScale M := by exact_mod_cast clockScale_pos hM
  unfold clockThreshold
  constructor
  · positivity
  · exact (div_le_one (lt_of_lt_of_le zero_lt_one hscale)).mpr hscale

theorem clockThreshold_small {M : ℕ} (hM : 0 < M) :
    (M : ℚ) ^ 2 * clockThreshold M ≤ 1 / 8 := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold clockThreshold clockScale
  push_cast
  apply le_of_eq
  field_simp

theorem momentOrder_large {M : ℕ} (H : ℕ) (hM : 0 < M) :
    8 * (M : ℚ) ≤ (momentOrder H M : ℚ) * clockThreshold M ^ H := by
  have hscale : (clockScale M : ℚ) ≠ 0 := by exact_mod_cast (clockScale_pos hM).ne'
  unfold momentOrder clockThreshold
  push_cast
  apply le_of_eq
  rw [one_div_pow]
  field_simp

theorem insertionConstant_pos (M : ℕ) : 0 < insertionConstant M := by
  unfold insertionConstant
  positivity

theorem relativeTolerance_pos (M : ℕ) {ε : ℚ} (hε : 0 < ε) :
    0 < relativeTolerance M ε := by
  unfold relativeTolerance
  have : (0 : ℚ) < insertionConstant M := by exact_mod_cast insertionConstant_pos M
  positivity

/-- Exponentially amplifying a natural ceiling dominates the original number. -/
theorem le_two_pow_ceil (q : ℚ) : q ≤ (2 : ℚ) ^ ⌈q⌉₊ := by
  apply (Nat.le_ceil q).trans
  exact_mod_cast (show ⌈q⌉₊ < 2 ^ ⌈q⌉₊ from Nat.lt_two_pow_self).le

/-- The explicit sweep count makes each marked high-moment tail at most `ε/8`. -/
theorem sweepCount_tail (H M : ℕ) (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) :
    (2 * R / relativeTolerance M ε) ^ momentOrder H M /
      (2 : ℚ) ^ sweepCount H M R ε ≤ ε / 8 := by
  let u := relativeTolerance M ε
  have hu : 0 < u := relativeTolerance_pos M hε
  have hbase0 : 0 ≤ 2 * R / u := by positivity
  have hp := pow_le_pow_left₀ hbase0 (le_two_pow_ceil (2 * R / u)) (momentOrder H M)
  have hεpow := le_two_pow_ceil (8 / ε)
  have hprod := mul_le_mul hp hεpow (by positivity : (0 : ℚ) ≤ 8 / ε)
    (by positivity : (0 : ℚ) ≤ ((2 : ℚ) ^ ⌈2 * R / u⌉₊) ^ momentOrder H M)
  have hlarge : (2 * R / u) ^ momentOrder H M * (8 / ε) ≤
      (2 : ℚ) ^ sweepCount H M R ε := by
    simpa only [sweepCount, ← pow_mul, ← pow_add, Nat.mul_comm] using hprod
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ sweepCount H M R ε)).mpr
  have hmul := mul_le_mul_of_nonneg_left hlarge (by positivity : (0 : ℚ) ≤ ε / 8)
  calc
    _ = (ε / 8) * ((2 * R / u) ^ momentOrder H M * (8 / ε)) := by
      field_simp
      rfl
    _ ≤ _ := hmul

/-- Every positive accuracy tolerance selects at least one sweep. -/
theorem sweepCount_pos (H M : ℕ) (R ε : ℚ) (hε : 0 < ε) : 0 < sweepCount H M R ε := by
  have h : 0 < ⌈(8 : ℚ) / ε⌉₊ := Nat.ceil_pos.mpr (by positivity)
  unfold sweepCount
  omega

/-- The integer threshold supplies the two exact scale inequalities. -/
theorem minimumWidth_spec (H M : ℕ) (R ε W : ℚ) (hε : 0 < ε)
    (hW : (minimumWidth H M R ε : ℚ) ≤ W) :
    2 * (H : ℚ) * sweepCount H M R ε ≤ relativeTolerance M ε * W ∧
      4 * (insertionConstant M : ℚ) ≤ ε * W := by
  have hu := relativeTolerance_pos M hε
  have hceil := Nat.le_ceil (max
    (2 * (H : ℚ) * sweepCount H M R ε / relativeTolerance M ε)
    (4 * (insertionConstant M : ℚ) / ε))
  have hmax : max
      (2 * (H : ℚ) * sweepCount H M R ε / relativeTolerance M ε)
      (4 * (insertionConstant M : ℚ) / ε) ≤ W := by
    unfold minimumWidth at hW
    push_cast at hW
    linarith
  constructor
  · have h := (le_max_left _ _).trans hmax
    exact (div_le_iff₀ hu).mp h |>.trans_eq (mul_comm _ _)
  · have h := (le_max_right _ _).trans hmax
    exact (div_le_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)

/-- Each positive physical width gives a positive coupling tolerance. -/
theorem halfTolerance_pos (M : ℕ) {ε W : ℚ} (hε : 0 < ε) (hW : 0 < W) :
    0 < relativeTolerance M ε * W / 2 := by
  have := relativeTolerance_pos M hε
  positivity

/-- The component width cancels from the normalized moment tail. -/
theorem width_tail (H M : ℕ) (R ε W : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (hW : 0 < W) :
    (R * W / (relativeTolerance M ε * W / 2)) ^ momentOrder H M /
      (2 : ℚ) ^ sweepCount H M R ε ≤ ε / 8 := by
  have hu := relativeTolerance_pos M hε
  have heq : R * W / (relativeTolerance M ε * W / 2) =
      2 * R / relativeTolerance M ε := by field_simp
  rw [heq]
  exact sweepCount_tail H M R ε hR hε

/-- The insertion estimate is at most `ε/2` at the broader endpoint. -/
theorem near_term (M : ℕ) (ε W z : ℚ) (hε : 0 < ε) (hW : 0 < W)
    (hwidth : 4 * (insertionConstant M : ℚ) ≤ ε * W)
    (hz : z ≤ 2 * relativeTolerance M ε * W) :
    (insertionConstant M : ℚ) * (2 * z + 1) / W ≤ ε / 2 := by
  have hC : (0 : ℚ) < insertionConstant M := by exact_mod_cast insertionConstant_pos M
  have hu : 4 * (insertionConstant M : ℚ) * relativeTolerance M ε = ε / 4 := by
    unfold relativeTolerance
    field_simp
    norm_num
  apply (div_le_iff₀ hW).mpr
  calc
    _ ≤ (4 * (insertionConstant M : ℚ) * relativeTolerance M ε) * W + insertionConstant M := by
      have h := mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℚ) ≤ 2 * insertionConstant M)
      nlinarith
    _ = (ε / 4) * W + insertionConstant M := by rw [hu]
    _ ≤ _ := by linarith

end SortingAdversary.Optimal.LocalParameters
