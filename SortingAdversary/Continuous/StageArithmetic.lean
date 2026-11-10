import SortingAdversary.Continuous.UniformStages
import Mathlib.Data.Nat.Size

/-!
# Integer tests and operand sizes during parameter generation

The two rational searches reduce to displayed natural-number comparisons.
The admitted recipe bounds their iteration counts, and the raw unreduced
integer operands have polynomial binary length. This also controls failed
tests before the least successful exponent is found.
-/

namespace SortingAdversary.Continuous.StageArithmetic

open EnclosureParameters UniformStages ParameterBounds

theorem contraction_ratio (d h : ℕ) :
    contraction d h = ((alphabet d h ^ h - 1 : ℕ) : ℚ) / (alphabet d h ^ h : ℕ) := by
  have hp : 0 < alphabet d h ^ h := pow_pos (alphabet_pos d h) h
  have hpq : (alphabet d h : ℚ) ^ h ≠ 0 := by
    exact_mod_cast hp.ne'
  unfold contraction
  rw [Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_pow, div_pow, one_pow]
  field_simp

/-- The moment search's exact rational test is an integer cross product. -/
theorem moment_test_iff (d h p : ℕ) :
    contraction d h ^ p ≤ 1 / (4 * (neighborhoodBound d h : ℚ)) ↔
      4 * neighborhoodBound d h * (alphabet d h ^ h - 1) ^ p ≤ (alphabet d h ^ h) ^ p := by
  have hS : (0 : ℚ) < (alphabet d h ^ h : ℕ) := by
    exact_mod_cast pow_pos (alphabet_pos d h) h
  have hM : (0 : ℚ) < 4 * neighborhoodBound d h := by
    have := neighborhoodBound_pos d h
    positivity
  rw [contraction_ratio, div_pow, div_le_div_iff₀ (pow_pos hS p) hM, one_mul]
  norm_cast
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The sweep search is likewise an integer comparison. -/
theorem sweep_test_iff (A D p t : ℕ) (hA : 0 < A) (hD : 0 < D) :
    (1 / 2 : ℚ) ^ t ≤ (1 / A) * (1 / D) ^ p / 2 ↔ 2 * A * D ^ p ≤ 2 ^ t := by
  have hAq : (0 : ℚ) < A := by exact_mod_cast hA
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have he : (1 / (A : ℚ)) * (1 / D) ^ p / 2 = 1 / (2 * A * D ^ p) := by
    rw [div_pow, one_pow]
    field_simp
  rw [div_pow, one_pow, he, one_div_le_one_div (by positivity) (by positivity)]
  norm_cast

theorem power_size (a e cap : ℕ) (ha : a ≤ cap) (he : e ≤ cap) :
    (a ^ e).size ≤ cap ^ 2 + 1 := by
  have ha' : a ≤ 2 ^ cap := ha.trans Nat.lt_two_pow_self.le
  have hp : a ^ e ≤ 2 ^ (cap ^ 2) := by
    calc
      a ^ e ≤ (2 ^ cap) ^ e := Nat.pow_le_pow_left ha' e
      _ ≤ (2 ^ cap) ^ cap := Nat.pow_le_pow_right (by positivity) he
      _ = 2 ^ (cap ^ 2) := by rw [← pow_mul, pow_two]
  simpa only [Nat.size_pow] using Nat.size_le_size hp

theorem iterated_power_size (a h p cap : ℕ) (ha : a ≤ cap) (hh : h ≤ cap) (hp : p ≤ cap) :
    ((a ^ h) ^ p).size ≤ cap ^ 3 + 1 := by
  have ha' : a ≤ 2 ^ cap := ha.trans Nat.lt_two_pow_self.le
  have hhp : h * p ≤ cap * cap := Nat.mul_le_mul hh hp
  have hn : (a ^ h) ^ p ≤ 2 ^ (cap ^ 3) := by
    calc
      (a ^ h) ^ p = a ^ (h * p) := (pow_mul _ _ _).symm
      _ ≤ (2 ^ cap) ^ (h * p) := Nat.pow_le_pow_left ha' _
      _ ≤ (2 ^ cap) ^ (cap * cap) := Nat.pow_le_pow_right (by positivity) hhp
      _ = 2 ^ (cap ^ 3) := by rw [← pow_mul]; congr 1; ring
  simpa only [Nat.size_pow] using Nat.size_le_size hn

theorem moment_operand_sizes (d h p cap : ℕ)
    (hS : alphabet d h ≤ cap) (hh : h ≤ cap) (hp : p ≤ cap)
    (hM : neighborhoodBound d h ≤ cap) :
    ((alphabet d h ^ h) ^ p).size ≤ cap ^ 3 + 1 ∧
      (4 * neighborhoodBound d h * (alphabet d h ^ h - 1) ^ p).size ≤ cap ^ 3 + cap + 3 := by
  refine ⟨iterated_power_size _ _ _ _ hS hh hp, ?_⟩
  have hbase : alphabet d h ≤ 2 ^ cap := hS.trans Nat.lt_two_pow_self.le
  have hn : (alphabet d h ^ h - 1) ^ p ≤ 2 ^ (cap ^ 3) := by
    calc
      _ ≤ (alphabet d h ^ h) ^ p := Nat.pow_le_pow_left (Nat.sub_le _ _) p
      _ = alphabet d h ^ (h * p) := (pow_mul _ _ _).symm
      _ ≤ (2 ^ cap) ^ (h * p) := Nat.pow_le_pow_left hbase _
      _ ≤ (2 ^ cap) ^ (cap * cap) := Nat.pow_le_pow_right (by positivity) (Nat.mul_le_mul hh hp)
      _ = 2 ^ (cap ^ 3) := by rw [← pow_mul]; congr 1; ring
  have hM' : neighborhoodBound d h ≤ 2 ^ cap := hM.trans Nat.lt_two_pow_self.le
  have hb : 4 * neighborhoodBound d h * (alphabet d h ^ h - 1) ^ p ≤
      2 ^ (cap ^ 3 + cap + 2) := by
    calc
      _ ≤ (2 ^ 2 * 2 ^ cap) * 2 ^ (cap ^ 3) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hM') hn
      _ = 2 ^ (cap ^ 3 + cap + 2) := by rw [← pow_add, ← pow_add]; congr 1; omega
  simpa only [Nat.size_pow, Nat.add_assoc] using Nat.size_le_size hb

theorem sweep_operand_sizes (A D p t cap : ℕ)
    (hA : A ≤ cap) (hD : D ≤ cap) (hp : p ≤ cap) (ht : t ≤ cap) :
    (2 * A * D ^ p).size ≤ cap ^ 2 + cap + 2 ∧ (2 ^ t).size ≤ cap + 1 := by
  have hA' : A ≤ 2 ^ cap := hA.trans Nat.lt_two_pow_self.le
  have hD' : D ≤ 2 ^ cap := hD.trans Nat.lt_two_pow_self.le
  have hd : D ^ p ≤ 2 ^ (cap ^ 2) := by
    calc
      _ ≤ (2 ^ cap) ^ p := Nat.pow_le_pow_left hD' _
      _ ≤ (2 ^ cap) ^ cap := Nat.pow_le_pow_right (by positivity) hp
      _ = 2 ^ (cap ^ 2) := by rw [← pow_mul, pow_two]
  have hb : 2 * A * D ^ p ≤ 2 ^ (cap ^ 2 + cap + 1) := by
    calc
      _ ≤ (2 ^ 1 * 2 ^ cap) * 2 ^ (cap ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA') hd
      _ = 2 ^ (cap ^ 2 + cap + 1) := by rw [← pow_add, ← pow_add]; congr 1; omega
  exact ⟨by simpa only [Nat.size_pow, Nat.add_assoc] using Nat.size_le_size hb,
    by simpa only [Nat.size_pow] using Nat.add_le_add_right ht 1⟩

end SortingAdversary.Continuous.StageArithmetic
