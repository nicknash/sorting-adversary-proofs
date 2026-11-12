import SortingAdversary.Continuous.Weights
import SortingAdversary.Continuous.Certificates
import SortingAdversary.Continuous.FiniteAveraging
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log

/-!
# Reduced dyadic anchors and the actual rounding rule

The geometric weight is charged at the *reduced* binary denominator of the
anchor returned by `RoundUp`.  This file connects that finite anchor code to
the rational number used in the executable state.  Distinct codes give
distinct coordinates, and reducing a grid point never increases its level.
-/

namespace SortingAdversary.Continuous

open Certificates FiniteAveraging

private theorem odd_numerator_coprime (i m : ℕ) :
    (2 * i + 1).Coprime (2 ^ m) := by
  apply Nat.Coprime.pow_right
  exact Nat.coprime_two_right.mpr ⟨i, rfl⟩

theorem DyadicAnchor.coordinate_num (c : DyadicAnchor) :
    c.coordinate.num = 2 * (c.2.val : ℤ) + 1 := by
  have h := Rat.num_div_eq_of_coprime
    (a := (2 * c.2.val + 1 : ℕ)) (b := (2 ^ (c.1 + 1) : ℕ))
    (by positivity) (by simpa using odd_numerator_coprime c.2.val (c.1 + 1))
  simpa [coordinate] using h

theorem DyadicAnchor.coordinate_den (c : DyadicAnchor) :
    c.coordinate.den = 2 ^ (c.1 + 1) := by
  have h := Rat.den_div_eq_of_coprime
    (a := (2 * c.2.val + 1 : ℕ)) (b := (2 ^ (c.1 + 1) : ℕ))
    (by positivity) (by simpa using odd_numerator_coprime c.2.val (c.1 + 1))
  have hn := congrArg Int.toNat h
  simpa [coordinate, Int.toNat_pow_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)] using hn

theorem DyadicAnchor.coordinate_injective : Function.Injective DyadicAnchor.coordinate := by
  intro c d h
  have hden := congrArg Rat.den h
  rw [coordinate_den, coordinate_den] at hden
  have hm : c.1 = d.1 := by
    have := pow_right_injective₀ (by norm_num : (0 : ℕ) < 2)
      (by norm_num : (2 : ℕ) ≠ 1) hden
    omega
  have hnum := congrArg Rat.num h
  rw [coordinate_num, coordinate_num] at hnum
  obtain ⟨m, i⟩ := c
  obtain ⟨m', j⟩ := d
  dsimp at hm
  subst m'
  congr 1
  apply Fin.ext
  dsimp at hnum
  omega

/-- A total executable decoder for reduced binary anchors. The modulus only
makes the function total on malformed inputs; it is inactive on an actual
interior dyadic coordinate. -/
def DyadicAnchor.ofRat (q : ℚ) : DyadicAnchor :=
  let m := Nat.log 2 q.den - 1
  ⟨m, ⟨(q.num.toNat / 2) % (2 ^ m), Nat.mod_lt _ (by positivity)⟩⟩

@[simp] theorem DyadicAnchor.ofRat_coordinate (c : DyadicAnchor) :
    ofRat c.coordinate = c := by
  have hm : Nat.log 2 c.coordinate.den - 1 = c.1 := by
    rw [coordinate_den, Nat.log_pow (by decide)]
    omega
  have hn : c.coordinate.num.toNat / 2 = c.2.val := by
    rw [coordinate_num]
    omega
  unfold ofRat
  apply Sigma.ext hm
  apply (Fin.heq_ext_iff (congrArg (fun m => 2 ^ m) hm)).mpr
  simp only [hm, hn, Nat.mod_eq_of_lt c.2.isLt]

theorem DyadicAnchor.ofRat_correct {q : ℚ}
    (hq : ∃ c : DyadicAnchor, c.coordinate = q) : (ofRat q).coordinate = q := by
  obtain ⟨c, rfl⟩ := hq
  simp

theorem onDyadicGrid_den_dvd {q : ℚ} {r : ℕ} (hq : OnDyadicGrid r q) : q.den ∣ 2 ^ r := by
  obtain ⟨z, rfl⟩ := hq
  have h := Rat.den_dvd z (2 ^ r : ℤ)
  rw [Rat.divInt_eq_div] at h
  norm_cast at h ⊢

/-- Every interior grid point has a unique reduced binary anchor code, whose
denominator exponent is no larger than the input grid exponent. -/
theorem exists_dyadicAnchor_of_grid {q : ℚ} {r : ℕ}
    (hq : OnDyadicGrid r q) (hpos : 0 < q) (hone : q < 1) :
    ∃ c : DyadicAnchor, c.coordinate = q ∧ c.1 + 1 ≤ r := by
  obtain ⟨e, her, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (onDyadicGrid_den_dvd hq)
  have hnum : 0 < q.num := Rat.num_pos.mpr hpos
  have hnumlt : q.num < (q.den : ℤ) := by
    have hqeq : q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
    rw [hqeq, div_lt_one (by exact_mod_cast q.den_pos)] at hone
    exact_mod_cast hone
  have hepos : 0 < e := by
    by_contra h
    have he0 : e = 0 := by omega
    simp only [he0, pow_zero] at he
    omega
  have hcop : q.num.natAbs.Coprime 2 := by
    apply q.reduced.of_dvd_right
    rw [he]
    exact dvd_pow_self 2 (by omega)
  have hodd := Nat.coprime_two_right.mp hcop
  obtain ⟨i, hi⟩ := hodd
  have heq : q.num = (2 * i + 1 : ℕ) := by
    have hn : (q.num.natAbs : ℤ) = q.num := by
      rw [Int.natCast_natAbs, abs_of_nonneg hnum.le]
    omega
  have hidx : i < 2 ^ (e - 1) := by
    have hpow : 2 ^ e = 2 ^ (e - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he, hpow, heq] at hnumlt
    have hh : 2 * i + 1 < 2 ^ (e - 1) * 2 := by exact_mod_cast hnumlt
    omega
  refine ⟨⟨e - 1, ⟨i, hidx⟩⟩, ?_, by change e - 1 + 1 ≤ r; omega⟩
  have hepred : e - 1 + 1 = e := by omega
  simp only [DyadicAnchor.coordinate, hepred]
  have hp : (q.den : ℚ) = (2 : ℚ) ^ e := by exact_mod_cast he
  have hn : (q.num : ℚ) = 2 * (i : ℚ) + 1 := by exact_mod_cast heq
  rw [← hp, ← hn, Rat.num_div_den]

theorem dyadicAnchor_level_le_grid (c : DyadicAnchor) {r : ℕ}
    (h : OnDyadicGrid r c.coordinate) : c.1 + 1 ≤ r := by
  obtain ⟨d, hd, hr⟩ := exists_dyadicAnchor_of_grid h c.coordinate_pos c.coordinate_lt_one
  have hdc : d = c := DyadicAnchor.coordinate_injective hd
  simpa [hdc] using hr

/-- For an interval strictly inside `(0,1)`, the chosen power-of-two spacing
has a negative exponent. -/
theorem spacing_exponent_neg {J : Interval} (hl : 0 < J.1) (hu : J.2 < 1)
    (hJ : J.1 < J.2) : Int.log 2 (J.2 - J.1) < 0 := by
  have hslt : spacing J < 1 := lt_of_le_of_lt (spacing_spec hJ).1 (by linarith)
  by_contra h
  have hz : 0 ≤ Int.log 2 (J.2 - J.1) := le_of_not_gt h
  have hsge : (1 : ℚ) ≤ spacing J := by
    unfold spacing
    exact one_le_zpow₀ (by norm_num) hz
  linarith

def roundingExponent (J : Interval) : ℕ := (-Int.log 2 (J.2 - J.1)).toNat

theorem spacing_eq_inverse_pow {J : Interval} (hl : 0 < J.1) (hu : J.2 < 1)
    (hJ : J.1 < J.2) : spacing J = 1 / (2 : ℚ) ^ roundingExponent J := by
  have hz := spacing_exponent_neg hl hu hJ
  have hr : (roundingExponent J : ℤ) = -Int.log 2 (J.2 - J.1) := by
    exact Int.toNat_of_nonneg (by omega)
  unfold spacing
  rw [← zpow_natCast, hr, zpow_neg]
  simp

theorem roundUp_onDyadicGrid {J : Interval} (hl : 0 < J.1) (hu : J.2 < 1)
    (hJ : J.1 < J.2) : OnDyadicGrid (roundingExponent J) (roundUp J) := by
  refine ⟨⌈J.1 / spacing J⌉, ?_⟩
  rw [roundUp, spacing_eq_inverse_pow hl hu hJ]
  ring

theorem roundUp_anchor {J : Interval} (hl : 0 < J.1) (hu : J.2 < 1)
    (hJ : J.1 < J.2) :
    ∃ c : DyadicAnchor, c.coordinate = roundUp J ∧
      J.2 - J.1 < 1 / (2 : ℚ) ^ c.1 := by
  have hmem := roundUp_mem hJ
  obtain ⟨c, hc, hlevel⟩ := exists_dyadicAnchor_of_grid
    (roundUp_onDyadicGrid hl hu hJ) (hl.trans_le hmem.1) (hmem.2.trans hu)
  refine ⟨c, hc, ?_⟩
  have hp : (2 : ℚ) ^ (c.1 + 1) ≤ (2 : ℚ) ^ roundingExponent J :=
    pow_le_pow_right₀ (by norm_num) hlevel
  have hs := (spacing_spec hJ).2
  rw [spacing_eq_inverse_pow hl hu hJ] at hs
  have hinv : 1 / (2 : ℚ) ^ roundingExponent J ≤ 1 / (2 : ℚ) ^ (c.1 + 1) :=
    one_div_le_one_div_of_le (by positivity) hp
  have he : 2 * (1 / (2 : ℚ) ^ (c.1 + 1)) = 1 / (2 : ℚ) ^ c.1 := by
    rw [pow_succ]
    field_simp
  linarith

end SortingAdversary.Continuous
