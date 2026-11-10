import SortingAdversary.Continuous.LocalEnclosure
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find

/-!
# Computable parameters for the finite enclosure calculation

These are the paper's exact choices: the least power of two at least `4M²`,
the least positive moment power passing its rational test, and the least
positive sweep count passing its rational test. Existence is proved before
`Nat.find` is used; all searches inspect decidable rational inequalities.
-/

namespace SortingAdversary.Continuous.EnclosureParameters

def neighborhoodBound (d h : ℕ) : ℕ := (d + 1) ^ (h + 1)

def alphabetExponent (d h : ℕ) : ℕ := Nat.clog 2 (4 * neighborhoodBound d h ^ 2)

def alphabet (d h : ℕ) : ℕ := 2 ^ alphabetExponent d h

theorem neighborhoodBound_pos (d h : ℕ) : 0 < neighborhoodBound d h := by
  unfold neighborhoodBound
  positivity

theorem alphabet_pos (d h : ℕ) : 0 < alphabet d h := by unfold alphabet; positivity

theorem alphabet_large (d h : ℕ) : 4 * neighborhoodBound d h ^ 2 ≤ alphabet d h :=
  Nat.le_pow_clog (by decide) _

theorem alphabetExponent_ge_two (d h : ℕ) : 2 ≤ alphabetExponent d h := by
  have hM : 1 ≤ neighborhoodBound d h ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (neighborhoodBound_pos d h).ne')
  have hlarge := alphabet_large d h
  by_contra hneg
  have he : alphabetExponent d h ≤ 1 := by omega
  have hsmall := Nat.pow_le_pow_right (by decide : 0 < 2) he
  change alphabet d h ≤ 2 at hsmall
  omega

theorem four_dvd_alphabet (d h : ℕ) : 4 ∣ alphabet d h := by
  change 2 ^ 2 ∣ 2 ^ alphabetExponent d h
  exact pow_dvd_pow 2 (alphabetExponent_ge_two d h)

def contraction (d h : ℕ) : ℚ := 1 - (1 / (alphabet d h : ℚ)) ^ h

theorem contraction_mem (d h : ℕ) : 0 ≤ contraction d h ∧ contraction d h < 1 := by
  have hS : (0 : ℚ) < alphabet d h := by exact_mod_cast alphabet_pos d h
  have hS1 : (1 : ℚ) ≤ alphabet d h := by exact_mod_cast alphabet_pos d h
  have hr : (0 : ℚ) < 1 / alphabet d h := by positivity
  have hr1 : (1 : ℚ) / alphabet d h ≤ 1 := (div_le_one hS).mpr hS1
  unfold contraction
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ hr.le hr1)
  · linarith [pow_pos hr h]

private theorem exists_positive_power_le {β target : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (htarget : 0 < target) :
    ∃ p : ℕ, 0 < p ∧ β ^ p ≤ target := by
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one htarget hβ1
  exact ⟨p + 1, Nat.succ_pos p,
    (pow_le_pow_of_le_one hβ0 hβ1.le (Nat.le_succ p)).trans hp.le⟩

theorem momentPower_exists (d h : ℕ) :
    ∃ p : ℕ, 0 < p ∧ contraction d h ^ p ≤ 1 / (4 * (neighborhoodBound d h : ℚ)) := by
  have hM : (0 : ℚ) < neighborhoodBound d h := by exact_mod_cast neighborhoodBound_pos d h
  exact exists_positive_power_le (contraction_mem d h).1 (contraction_mem d h).2 (by positivity)

def momentPower (d h : ℕ) : ℕ := Nat.find (momentPower_exists d h)

theorem momentPower_pos (d h : ℕ) : 0 < momentPower d h := (Nat.find_spec (momentPower_exists d h)).1

theorem momentPower_spec (d h : ℕ) :
    contraction d h ^ momentPower d h ≤ 1 / (4 * (neighborhoodBound d h : ℚ)) :=
  (Nat.find_spec (momentPower_exists d h)).2

theorem sweepCount_exists (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    ∃ t : ℕ, 0 < t ∧ (1 / 2 : ℚ) ^ t ≤ α * δ ^ momentPower d h / 2 := by
  exact exists_positive_power_le (by norm_num) (by norm_num) (by positivity)

def sweepCount (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) : ℕ :=
  Nat.find (sweepCount_exists d h δ α hδ hα)

theorem sweepCount_pos (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    0 < sweepCount d h δ α hδ hα := (Nat.find_spec (sweepCount_exists d h δ α hδ hα)).1

theorem sweepCount_spec (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    (1 / 2 : ℚ) ^ sweepCount d h δ α hδ hα ≤ α * δ ^ momentPower d h / 2 :=
  (Nat.find_spec (sweepCount_exists d h δ α hδ hα)).2

def radius (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) : ℕ :=
  h * sweepCount d h δ α hδ hα + 1

def retainedBound (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) : ℕ :=
  2 * (d + 1) ^ (radius d h δ α hδ hα + 1)

def enumerationBound (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) : ℕ :=
  alphabet d h ^ (retainedBound d h δ α hδ hα * sweepCount d h δ α hδ hα)

theorem enumerationBound_pos (d h : ℕ) (δ α : ℚ) (hδ : 0 < δ) (hα : 0 < α) :
    0 < enumerationBound d h δ α hδ hα := pow_pos (alphabet_pos d h) _

end SortingAdversary.Continuous.EnclosureParameters
