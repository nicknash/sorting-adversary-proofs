import SortingAdversary.Optimal.MeasuredOracleBounds
import SortingAdversary.Optimal.RationalBitWork

/-!
# Operand widths throughout exact local counting and rational comparison

Stored DP entries and every partial transition/read sum obey one common
polynomial width bound. The actual count pairs passed to Euclidean
normalization satisfy that same bound; the concrete normalization profiles
therefore have polynomial binary charges. The final comparison statements
refer to the actual branch/CDF values used by the controller.
-/

namespace SortingAdversary.Optimal.LocalOracleBitBounds

open PrimitiveWork SubsetWork LocalDPWork RepresentationWork WidthRepair
open MeasuredLocalOracle MeasuredOracleBounds

variable {n b K : ℕ} {s : State n}

theorem allowance_le (N c : ℕ) (hb : b ≤ N) (hK : K ≤ c * N) :
    b * (Nat.log 2 (K + 1) + 1) + 1 ≤ bitBound N c := by
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul hb (Nat.add_le_add_right
    (Nat.log_mono_right (Nat.add_le_add_right hK 1)) 1)

theorem stored_bits (data : Input b K) (k : ℕ) (hk : k ≤ K)
    {entry : Mask b × ℕ} (hentry : entry ∈ (table data (enumerate b).value k).value)
    (N c : ℕ) (hb : b ≤ N) (hK : K ≤ c * N) :
    Nat.size entry.2 ≤ bitBound N c :=
  (stored_size data k hk hentry).trans (allowance_le N c hb hK)

theorem transition_partial_bits (data : Input b K) (k : ℕ) (hk : k + 1 ≤ K) (J : Mask b)
    (entries : Table b) (h : entries.Sublist (table data (enumerate b).value k).value)
    (N c : ℕ) (hb : b ≤ N) (hK : K ≤ c * N) :
    Nat.size (stepSum data k J entries).value ≤ bitBound N c :=
  (stepSum_partial_size data k hk J entries h).trans (allowance_le N c hb hK)

theorem read_partial_bits (data : Input b K) (k : ℕ) (hk : k ≤ K) (J : Mask b)
    (entries : Table b) (h : entries.Sublist (table data (enumerate b).value k).value)
    (N c : ℕ) (hb : b ≤ N) (hK : K ≤ c * N) :
    Nat.size (read J entries).value ≤ bitBound N c :=
  (read_partial_size data k hk J entries h).trans (allowance_le N c hb hK)

/-- This applies simultaneously to each recursive suffix of every real
table scan, so intermediate additions cannot hide larger integers. -/
theorem table_scan_bits (data : Input b K) (k : ℕ) (hk : k ≤ K)
    (entries : Table b) (h : entries.Sublist (table data (enumerate b).value k).value)
    (N c : ℕ) (hb : b ≤ N) (hK : K ≤ c * N) :
    (∀ entry ∈ entries, Nat.size entry.2 ≤ bitBound N c) ∧
      (∀ J, Nat.size (read J entries).value ≤ bitBound N c) ∧
      (k + 1 ≤ K → ∀ J, Nat.size (stepSum data k J entries).value ≤ bitBound N c) := by
  refine ⟨fun entry he => stored_bits data k hk (h.subset he) N c hb hK,
    fun J => read_partial_bits data k hk J entries h N c hb hK, ?_⟩
  intro hn J
  exact transition_partial_bits data k hn J entries h N c hb hK

theorem table_scan_bits_polynomial (data : Input b K) (k : ℕ) (hk : k ≤ K)
    (entries : Table b) (h : entries.Sublist (table data (enumerate b).value k).value)
    (n c : ℕ) (hb : b ≤ 2 * n) (hK : K ≤ c * (2 * n)) :
    (∀ entry ∈ entries, Nat.size entry.2 ≤ countBits n c) ∧
      (∀ J, Nat.size (read J entries).value ≤ countBits n c) ∧
      (k + 1 ≤ K → ∀ J, Nat.size (stepSum data k J entries).value ≤ countBits n c) := by
  have ht := table_scan_bits data k hk entries h (2 * n) c hb hK
  have ha : bitBound (2 * n) c ≤ countBits n c :=
    (Nat.le_succ _).trans (bitBound_double_le n c)
  exact ⟨fun entry he => (ht.1 entry he).trans ha,
    fun J => (ht.2.1 J).trans ha, fun hk J => (ht.2.2 hk J).trans ha⟩

/-- The actual mask lists and actual stored layers have at most `N` cells
under the logarithmic cap, not just their abstract state spaces. -/
theorem table_length_le (data : Input b K) (k N : ℕ) (hN : N ≠ 0) (hb : b ≤ Nat.log 2 N) :
    (table data (enumerate b).value k).value.length ≤ N := by
  rw [LocalDPWork.table_length, enumerate_length]
  exact Nat.pow_le_of_le_log hN hb

theorem branch_integer_bits (a : LocalAccess s) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size (branchCounts (prepare a).value r x y).value.1 ≤ countBits n c ∧
      Nat.size (branchCounts (prepare a).value r x y).value.2 ≤ countBits n c := by
  have h := MeasuredOracleBudget.branchCounts_sizes (prepare a).value r x y (2 * n) c
    (by omega) (hK.trans (Nat.mul_le_mul_left c (by omega : n ≤ 2 * n)))
  have hb := bitBound_double_le n c
  omega

theorem cdf_integer_bits (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    Nat.size (cdfCounts (prepare a).value r x cut).value.1 ≤ countBits n c ∧
      Nat.size (cdfCounts (prepare a).value r x cut).value.2 ≤ countBits n c := by
  have h := MeasuredOracleBudget.cdfCounts_sizes (prepare a).value r x cut (2 * n) c
    (by omega) (hK.trans (Nat.mul_le_mul_left c (by omega : n ≤ 2 * n)))
  have hb := bitBound_double_le n c
  omega

def ratioBits (n c : ℕ) : ℕ := (6 * countBits n c + 10) * (countBits n c + 1) ^ 2

theorem branch_ratio_bitWork (a : LocalAccess s) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    let pair := (branchCounts (prepare a).value r x y).value
    (RationalBitWork.ratio pair.1 pair.2).bitWork ≤ ratioBits n c := by
  have h := branch_integer_bits a r x y c hK
  exact RationalBitWork.ratio_bitWork_polynomial _ _ (countBits n c) h.1 h.2

theorem cdf_ratio_bitWork (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    let pair := (cdfCounts (prepare a).value r x cut).value
    (RationalBitWork.ratio pair.1 pair.2).bitWork ≤ ratioBits n c := by
  have h := cdf_integer_bits a r x cut c hK
  exact RationalBitWork.ratio_bitWork_polynomial _ _ (countBits n c) h.1 h.2

theorem branch_ratio_value (a : LocalAccess s) (r : ℕ) (x y : Fin n) :
    let pair := (branchCounts (prepare a).value r x y).value
    (RationalBitWork.ratio pair.1 pair.2).result.value = (branch a r x y).value := by
  dsimp only
  rw [RationalBitWork.ratio_result]
  rfl

theorem cdf_ratio_value (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut : ℕ) :
    let pair := (cdfCounts (prepare a).value r x cut).value
    (RationalBitWork.ratio pair.1 pair.2).result.value = (cdf a r x cut).value := by
  dsimp only
  rw [RationalBitWork.ratio_result]
  rfl

theorem stopping_comparator_bitWork (a : LocalAccess s) (r : ℕ) (x y : Fin n) (c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (RationalBitWork.lessEqual (branch a r y x).value (branch a r x y).value).bitWork ≤
      7 * (2 * countBits n c + 1) ^ 2 :=
  RationalBitWork.lessEqual_bitWork_le _ _ (countBits n c)
    (branch_sizes_polynomial a r y x c hK) (branch_sizes_polynomial a r x y c hK)

theorem quarter_sizes :
    Nat.size (1 / 4 : ℚ).num.natAbs ≤ 3 ∧ Nat.size (1 / 4 : ℚ).den ≤ 3 := by
  simpa only [RationalWork.ratio_value, Nat.cast_one, Nat.cast_ofNat] using
    And.intro ((RationalWork.ratio_num_size 1 4).trans (by decide : Nat.size 1 ≤ 3))
      ((RationalWork.ratio_den_size_of_ne_zero 1 4 (by decide)).trans (by decide : Nat.size 4 ≤ 3))

theorem three_quarter_sizes :
    Nat.size (3 / 4 : ℚ).num.natAbs ≤ 3 ∧ Nat.size (3 / 4 : ℚ).den ≤ 3 := by
  simpa only [RationalWork.ratio_value, Nat.cast_ofNat] using
    And.intro ((RationalWork.ratio_num_size 3 4).trans (by decide : Nat.size 3 ≤ 3))
      ((RationalWork.ratio_den_size_of_ne_zero 3 4 (by decide)).trans (by decide : Nat.size 4 ≤ 3))

theorem calibration_comparator_bitWork (a : LocalAccess s) (r : ℕ) (x : Fin n) (cut c : ℕ)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (RationalBitWork.lessEqual (1 / 4) (cdf a r x cut).value).bitWork ≤
        7 * (2 * (countBits n c + 3) + 1) ^ 2 ∧
      (RationalBitWork.lessEqual (3 / 4) (cdf a r x cut).value).bitWork ≤
        7 * (2 * (countBits n c + 3) + 1) ^ 2 := by
  have hq := cdf_sizes_polynomial a r x cut c hK
  have hq' : Nat.size (cdf a r x cut).value.num.natAbs ≤ countBits n c + 3 ∧
      Nat.size (cdf a r x cut).value.den ≤ countBits n c + 3 := by omega
  exact ⟨RationalBitWork.lessEqual_bitWork_le _ _ _ (by have := quarter_sizes; omega) hq',
    RationalBitWork.lessEqual_bitWork_le _ _ _ (by have := three_quarter_sizes; omega) hq'⟩

end SortingAdversary.Optimal.LocalOracleBitBounds
