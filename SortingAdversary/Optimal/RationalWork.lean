import SortingAdversary.Optimal.PrimitiveWork
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counted Euclidean normalization of exact rational numbers

Rational construction is not charged as one primitive operation. An explicit
Euclidean loop computes the common divisor, after which two exact quotients
form the reduced numerator and denominator. The loop has a bound linear in
the binary lengths of its inputs, and normalization never increases either
input's absolute size. Arithmetic primitives here are integer comparison,
remainder, quotient, addition and multiplication; their operand sizes are
bounded separately for the controller's bit-cost accounting.
-/

namespace SortingAdversary.Optimal.RationalWork

open PrimitiveWork

/-- With the larger argument first, one Euclidean remainder is less than
half that argument. This gives a binary-length decrease even if the divisor
and remainder have the same binary length. -/
theorem twice_mod_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : 2 * (a % b) < a := by
  have hr := Nat.mod_lt a hb
  by_cases hhalf : 2 * b ≤ a
  · omega
  · rw [Nat.mod_eq_sub_mod hba, Nat.mod_eq_of_lt (by omega : a - b < b)]
    omega

theorem size_mod_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : Nat.size (a % b) < Nat.size a := by
  have hr := twice_mod_lt hb hba
  have ha : 0 < a := hb.trans_le hba
  have hs : 0 < Nat.size a := Nat.size_pos.mpr ha
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hp := Nat.lt_size_self a
  rw [hk, pow_succ] at hp
  have hrem : a % b < 2 ^ k := by nlinarith
  have hsize := Nat.size_le.mpr hrem
  omega

/-- The order certificate is erased. Every recursive call performs the
actual remainder, with one zero test and one loop step. -/
def euclid (a b : ℕ) (_hba : b ≤ a) : Result ℕ :=
  if hb : b = 0 then ⟨a, 1⟩
  else
    let result := euclid b (a % b) (Nat.le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero hb)))
    ⟨result.value, result.work + 3⟩
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

@[simp] theorem euclid_value (a b : ℕ) (hba : b ≤ a) : (euclid a b hba).value = Nat.gcd a b := by
  unfold euclid
  split
  · simp_all
  · rename_i hb
    dsimp only
    rw [euclid_value b (a % b)]
    calc
      Nat.gcd b (a % b) = Nat.gcd (a % b) b := Nat.gcd_comm ..
      _ = Nat.gcd b a := (Nat.gcd_rec b a).symm
      _ = Nat.gcd a b := Nat.gcd_comm ..
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

theorem euclid_work_le (a b : ℕ) (hba : b ≤ a) :
    (euclid a b hba).work ≤ 3 * (Nat.size a + Nat.size b) + 1 := by
  unfold euclid
  split
  · dsimp only; omega
  · rename_i hb
    have ih := euclid_work_le b (a % b) (Nat.le_of_lt (Nat.mod_lt a (Nat.pos_of_ne_zero hb)))
    have hs := size_mod_lt (Nat.pos_of_ne_zero hb) hba
    dsimp only
    omega
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

/-- One initial comparison places the larger integer first. -/
def gcd (a b : ℕ) : Result ℕ :=
  if h : b ≤ a then
    let result := euclid a b h
    ⟨result.value, result.work + 1⟩
  else
    let result := euclid b a (Nat.le_of_lt (Nat.lt_of_not_ge h))
    ⟨result.value, result.work + 1⟩

@[simp] theorem gcd_value (a b : ℕ) : (gcd a b).value = Nat.gcd a b := by
  simp only [gcd]
  split <;> simp only [euclid_value, Nat.gcd_comm]

theorem gcd_work_le (a b : ℕ) :
    (gcd a b).work ≤ 3 * (Nat.size a + Nat.size b) + 2 := by
  simp only [gcd]
  split
  · rename_i h
    have he := euclid_work_le a b h
    dsimp only
    omega
  · rename_i h
    have he := euclid_work_le b a (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp only
    omega

/-- Construct the rational directly from the measured gcd result. The
proofs certify the two quotients; they do not execute another gcd. -/
def normalize (num : ℤ) (den : ℕ) (hden : den ≠ 0) : Result ℚ :=
  let divisor := gcd num.natAbs den
  ⟨{ num := num / (divisor.value : ℤ)
     den := den / divisor.value
     den_nz := Rat.normalize.den_nz hden (gcd_value num.natAbs den)
     reduced := Rat.normalize.reduced hden (gcd_value num.natAbs den) },
    divisor.work + 6⟩

@[simp] theorem normalize_value (num : ℤ) (den : ℕ) (hden : den ≠ 0) :
    (normalize num den hden).value = Rat.normalize num den hden := by
  apply Rat.ext
  · simp only [normalize, gcd_value, Rat.num_normalize]
  · simp only [normalize, gcd_value, Rat.den_normalize]

theorem normalize_work_le (num : ℤ) (den : ℕ) (hden : den ≠ 0) :
    (normalize num den hden).work ≤ 3 * (Nat.size num.natAbs + Nat.size den) + 8 := by
  have h := gcd_work_le num.natAbs den
  change _ + 6 ≤ _
  omega

theorem normalize_num_le (num : ℤ) (den : ℕ) (hden : den ≠ 0) :
    (normalize num den hden).value.num.natAbs ≤ num.natAbs := by
  rw [normalize_value, Rat.num_normalize,
    Int.natAbs_ediv_of_dvd (Rat.normalize.dvd_num rfl), Int.natAbs_natCast]
  exact Nat.div_le_self _ _

theorem normalize_den_le (num : ℤ) (den : ℕ) (hden : den ≠ 0) :
    (normalize num den hden).value.den ≤ den := by
  rw [normalize_value, Rat.den_normalize]
  exact Nat.div_le_self _ _

theorem normalize_sizes (num : ℤ) (den : ℕ) (hden : den ≠ 0) :
    Nat.size (normalize num den hden).value.num.natAbs ≤ Nat.size num.natAbs ∧
      Nat.size (normalize num den hden).value.den ≤ Nat.size den :=
  ⟨Nat.size_le_size (normalize_num_le num den hden),
    Nat.size_le_size (normalize_den_le num den hden)⟩

/-- A total exact natural-count ratio, including the standard zero-denominator
value used by the semantic rational field. -/
def ratio (num den : ℕ) : Result ℚ :=
  if hden : den = 0 then ⟨0, 1⟩
  else
    let result := normalize (num : ℤ) den hden
    ⟨result.value, result.work + 2⟩

@[simp] theorem ratio_value (num den : ℕ) : (ratio num den).value = (num : ℚ) / den := by
  simp only [ratio]
  split
  · simp_all
  · rw [normalize_value, Rat.normalize_eq_mkRat, Rat.mkRat_eq_div]
    simp

theorem ratio_work_le (num den : ℕ) :
    (ratio num den).work ≤ 3 * (Nat.size num + Nat.size den) + 10 := by
  simp only [ratio]
  split
  · dsimp only; omega
  · rename_i hd
    have hn := normalize_work_le (num : ℤ) den hd
    simp only [Int.natAbs_natCast] at hn
    dsimp only
    omega

theorem ratio_num_size (num den : ℕ) :
    Nat.size (ratio num den).value.num.natAbs ≤ Nat.size num := by
  simp only [ratio]
  split
  · simp
  · simpa only [Int.natAbs_natCast] using (normalize_sizes (num : ℤ) den ‹den ≠ 0›).1

theorem ratio_den_size_of_ne_zero (num den : ℕ) (hden : den ≠ 0) :
    Nat.size (ratio num den).value.den ≤ Nat.size den := by
  simp only [ratio, dif_neg hden]
  exact (normalize_sizes (num : ℤ) den hden).2

theorem ratio_den_size (num den : ℕ) :
    Nat.size (ratio num den).value.den ≤ Nat.size den + 1 := by
  by_cases hd : den = 0
  · simp [ratio, hd]
  · exact (ratio_den_size_of_ne_zero num den hd).trans (Nat.le_succ _)

/-- Size arithmetic for the cross products used by rational operations. -/
theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_add_le (a b : ℕ) :
    Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.le_max_left (Nat.size a) (Nat.size b)))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.le_max_right (Nat.size a) (Nat.size b)))
  apply Nat.size_le.mpr
  rw [pow_succ]
  omega

theorem size_int_mul_le (a b : ℤ) :
    Nat.size (a * b).natAbs ≤ Nat.size a.natAbs + Nat.size b.natAbs := by
  rw [Int.natAbs_mul]
  exact size_mul_le _ _

theorem size_int_add_le (a b : ℤ) :
    Nat.size (a + b).natAbs ≤ max (Nat.size a.natAbs) (Nat.size b.natAbs) + 1 :=
  (Nat.size_le_size (Int.natAbs_add_le a b)).trans (size_add_le _ _)

theorem size_int_sub_le (a b : ℤ) :
    Nat.size (a - b).natAbs ≤ max (Nat.size a.natAbs) (Nat.size b.natAbs) + 1 :=
  (Nat.size_le_size (Int.natAbs_sub_le a b)).trans (size_add_le _ _)

end SortingAdversary.Optimal.RationalWork
