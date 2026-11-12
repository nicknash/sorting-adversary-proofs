import SortingAdversary.Continuous.EnclosureParameters
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Elementary bounds for the exact parameter searches

The calibration uses least successful rational tests. These explicit natural
number envelopes bound those searches without changing their chosen values.
They allow a capped arithmetic program to reject unaffordable stages before
constructing the large parameter integers.
-/

namespace SortingAdversary.Continuous.ParameterBounds

open EnclosureParameters

/-- A rational form of the elementary geometric decay bound. -/
theorem geometric_le_reciprocal (ε : ℚ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (p : ℕ) :
    (1 - ε) ^ p ≤ 1 / (1 + (p : ℚ) * ε) := by
  have hb : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
  have hprod : ∀ p : ℕ, (1 - ε) ^ p * (1 + (p : ℚ) * ε) ≤ 1 := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      have hn : (0 : ℚ) ≤ p := by positivity
      have he : (1 - ε) * (1 + ((p : ℚ) + 1) * ε) ≤ 1 + (p : ℚ) * ε := by
        nlinarith [sq_nonneg ε, mul_nonneg hn (sq_nonneg ε)]
      have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hb p)
      calc
        (1 - ε) ^ (p + 1) * (1 + ((p + 1 : ℕ) : ℚ) * ε) =
            (1 - ε) ^ p * ((1 - ε) * (1 + ((p : ℚ) + 1) * ε)) := by
              rw [pow_succ, Nat.cast_add, Nat.cast_one]
              ring
        _ ≤ (1 - ε) ^ p * (1 + (p : ℚ) * ε) := hh
        _ ≤ 1 := ih
  exact (le_div_iff₀ (by positivity : (0 : ℚ) < 1 + (p : ℚ) * ε)).mpr (hprod p)

def alphabetExponentBound (d h : ℕ) : ℕ := 4 * neighborhoodBound d h ^ 2

def alphabetBound (d h : ℕ) : ℕ := 2 ^ alphabetExponentBound d h

theorem alphabetExponent_le (d h : ℕ) : alphabetExponent d h ≤ alphabetExponentBound d h :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))

theorem alphabet_le (d h : ℕ) : alphabet d h ≤ alphabetBound d h :=
  Nat.pow_le_pow_right (by decide) (alphabetExponent_le d h)

def momentBound (d h : ℕ) : ℕ := 4 * neighborhoodBound d h * alphabet d h ^ h

theorem momentBound_pos (d h : ℕ) : 0 < momentBound d h := by
  unfold momentBound
  have := neighborhoodBound_pos d h
  have := alphabet_pos d h
  positivity

theorem momentPower_le (d h : ℕ) : momentPower d h ≤ momentBound d h := by
  apply Nat.find_min'
  refine ⟨momentBound_pos d h, ?_⟩
  have hS : (0 : ℚ) < alphabet d h := by exact_mod_cast alphabet_pos d h
  have hS1 : (1 : ℚ) ≤ alphabet d h := by exact_mod_cast alphabet_pos d h
  have hM : (0 : ℚ) < neighborhoodBound d h := by exact_mod_cast neighborhoodBound_pos d h
  have hε0 : (0 : ℚ) ≤ (1 / alphabet d h) ^ h := by positivity
  have hε1 : (1 / (alphabet d h : ℚ)) ^ h ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hS).mpr hS1)
  have hh := geometric_le_reciprocal ((1 / alphabet d h) ^ h) hε0 hε1 (momentBound d h)
  have he : (momentBound d h : ℚ) * (1 / (alphabet d h : ℚ)) ^ h =
      4 * neighborhoodBound d h := by
    unfold momentBound
    push_cast
    rw [div_pow, one_pow]
    field_simp
  rw [he] at hh
  exact hh.trans (one_div_le_one_div_of_le (by positivity) (by linarith))

/-- A fixed arithmetic expression can use this envelope without computing
the least alphabet exponent first. -/
def momentEnvelope (d h : ℕ) : ℕ := 4 * neighborhoodBound d h * alphabetBound d h ^ h

theorem momentPower_le_envelope (d h : ℕ) : momentPower d h ≤ momentEnvelope d h := by
  apply (momentPower_le d h).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (alphabet_le d h) h)

def sweepBound (d h A D : ℕ) : ℕ := 2 * A * D ^ momentPower d h

theorem sweepCount_le (d h A D : ℕ) (hA : 0 < A) (hD : 0 < D)
    (hδ : (0 : ℚ) < 1 / D) (hα : (0 : ℚ) < 1 / A) :
    sweepCount d h (1 / D) (1 / A) hδ hα ≤ sweepBound d h A D := by
  apply Nat.find_min'
  have hT : 0 < sweepBound d h A D := by unfold sweepBound; positivity
  refine ⟨hT, ?_⟩
  have hAq : (0 : ℚ) < A := by exact_mod_cast hA
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hTq : (0 : ℚ) < sweepBound d h A D := by exact_mod_cast hT
  have hpow : (sweepBound d h A D : ℚ) ≤ 2 ^ sweepBound d h A D := by
    exact_mod_cast (Nat.lt_two_pow_self (n := sweepBound d h A D)).le
  have hh := one_div_le_one_div_of_le hTq hpow
  have he : (1 : ℚ) / sweepBound d h A D = (1 / A) * (1 / D) ^ momentPower d h / 2 := by
    unfold sweepBound
    push_cast
    rw [div_pow, one_pow]
    field_simp
  simpa only [div_pow, one_pow, he] using hh

def sweepEnvelope (d h A D : ℕ) : ℕ := 2 * A * D ^ momentEnvelope d h

theorem sweepCount_le_envelope (d h A D : ℕ) (hA : 0 < A) (hD : 0 < D)
    (hδ : (0 : ℚ) < 1 / D) (hα : (0 : ℚ) < 1 / A) :
    sweepCount d h (1 / D) (1 / A) hδ hα ≤ sweepEnvelope d h A D := by
  apply (sweepCount_le d h A D hA hD hδ hα).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD (momentPower_le_envelope d h))

def retainedEnvelope (d h A D : ℕ) : ℕ :=
  2 * (d + 1) ^ (h * sweepEnvelope d h A D + 2)

def enumerationEnvelope (d h A D : ℕ) : ℕ :=
  alphabetBound d h ^ (retainedEnvelope d h A D * sweepEnvelope d h A D)

theorem retainedBound_le_envelope (d h A D : ℕ) (hA : 0 < A) (hD : 0 < D)
    (hδ : (0 : ℚ) < 1 / D) (hα : (0 : ℚ) < 1 / A) :
    retainedBound d h (1 / D) (1 / A) hδ hα ≤ retainedEnvelope d h A D := by
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by omega)
  have hh := Nat.mul_le_mul_left h (sweepCount_le_envelope d h A D hA hD hδ hα)
  change h * sweepCount d h (1 / D) (1 / A) hδ hα + 1 + 1 ≤ _
  omega

theorem enumerationBound_le_envelope (d h A D : ℕ) (hA : 0 < A) (hD : 0 < D)
    (hδ : (0 : ℚ) < 1 / D) (hα : (0 : ℚ) < 1 / A) :
    enumerationBound d h (1 / D) (1 / A) hδ hα ≤ enumerationEnvelope d h A D := by
  unfold enumerationBound enumerationEnvelope
  exact Nat.pow_le_pow_left (alphabet_le d h) _ |>.trans
    (Nat.pow_le_pow_right (by unfold alphabetBound; positivity)
      (Nat.mul_le_mul (retainedBound_le_envelope d h A D hA hD hδ hα)
        (sweepCount_le_envelope d h A D hA hD hδ hα)))

end SortingAdversary.Continuous.ParameterBounds
