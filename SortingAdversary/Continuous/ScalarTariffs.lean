import SortingAdversary.Continuous.Dyadic
import SortingAdversary.Continuous.ComparableDensity

/-!
# The logarithmic gain of the actual rounding rule

The central and middle-half estimates are converted into the reduced-anchor
tariff used by the global accounting. The strict inequalities include the
rounding slack, rather than assuming a tariff as an input certificate.
-/

namespace SortingAdversary.Continuous

theorem log2_strictMono {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    log2 x < log2 y :=
  (div_lt_div_iff_of_pos_right log_two_pos).mpr (Real.log_lt_log hx hxy)

theorem central_density_tariff {w f : ℝ} {m : ℕ}
    (hw : 0 < w) (hlen : w < 1 / (2 : ℝ) ^ m)
    (hf : 1 / (16 * w) ≤ f) :
    (m : ℝ) - 4 < log2 f := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hfw : (2 : ℝ) ^ m / 16 < 1 / (16 * w) := by
    have hprod : w * 2 ^ m < 1 := (lt_div_iff₀ hp).mp hlen
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 16) (by positivity)).mpr
    nlinarith
  have hlog := log2_strictMono (div_pos hp (by norm_num)) (hfw.trans_le hf)
  have h16 : log2 16 = 4 := by
    have h : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h, log2_pow, log2_two]
    norm_num
  simpa [log2_div hp.ne' (by norm_num : (16 : ℝ) ≠ 0), log2_pow, h16] using hlog

theorem middle_density_log_lower {W f : ℝ} {B : ℕ}
    (hW : 0 < W) (hf : (1 / 4 : ℝ) ^ B / W ≤ f) :
    log2 (1 / W) - 2 * B ≤ log2 f := by
  have hp : (0 : ℝ) < (1 / 4 : ℝ) ^ B / W := by positivity
  have hquarter : log2 (1 / 4) = -2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [log2_div (by norm_num) (by norm_num), log2_one, h4, log2_pow, log2_two]
    norm_num
  have h := log2_mono hp hf
  rw [log2_div (by positivity) hW.ne', log2_pow, hquarter] at h
  rw [log2_div (by norm_num) hW.ne', log2_one]
  linarith

theorem small_width_log {W : ℝ} {k B : ℕ}
    (hW : 0 < W) (hsmall : W < 1 / (2 : ℝ) ^ (2 * k * B)) :
    2 * (k : ℝ) * B < log2 (1 / W) := by
  have h := log2_strictMono hW hsmall
  rw [log2_div (by norm_num) (by positivity), log2_one, log2_pow, log2_two] at h
  rw [log2_div (by norm_num) hW.ne', log2_one]
  push_cast at h
  linarith

theorem middle_rounding_level {W : ℝ} {m : ℕ}
    (hW : 0 < W) (hlen : W / 2 < 1 / (2 : ℝ) ^ m) :
    (m : ℝ) < log2 (1 / W) + 1 := by
  have h := log2_strictMono (div_pos hW (by norm_num)) hlen
  rw [log2_div hW.ne' (by norm_num), log2_two,
    log2_div (by norm_num) (by positivity), log2_one, log2_pow, log2_two] at h
  rw [log2_div (by norm_num) hW.ne', log2_one]
  linarith

/-- A failed calibrated test gives both a gain larger than `k` and the
same reduced-level tariff as a successful central test. -/
theorem failed_density_tariffs {W f : ℝ} {k B m : ℕ}
    (hk : 64 ≤ k) (hB : 1 ≤ B) (hW : 0 < W)
    (hsmall : W < 1 / (2 : ℝ) ^ (2 * k * B))
    (hf : (1 / 4 : ℝ) ^ B / W ≤ f)
    (hlen : W / 2 < 1 / (2 : ℝ) ^ m) :
    (k : ℝ) < log2 f ∧ stopMass k * m - 4 < log2 f := by
  let L := log2 (1 / W)
  have hL : 2 * (k : ℝ) * B < L := small_width_log hW hsmall
  have hg : L - 2 * B ≤ log2 f := middle_density_log_lower hW hf
  have hm : (m : ℝ) < L + 1 := middle_rounding_level hW hlen
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hk0 : (0 : ℝ) < k := by linarith
  have hs := stopMass_pos (show (1 : ℝ) < k by linarith)
  have hs1 : stopMass k < 1 := by
    unfold stopMass
    have : (0 : ℝ) < 1 / k := by positivity
    linarith
  have heq : (k : ℝ) * stopMass k = k - 1 := by
    unfold stopMass
    field_simp
  have heqL := congrArg (fun z : ℝ => z * L) heq
  have hgain : (k : ℝ) < L - 2 * B := by nlinarith
  have hdiscount : stopMass k * L < L - 2 * B := by
    apply (mul_lt_mul_iff_right₀ hk0).mp
    nlinarith [heqL]
  have hround := mul_lt_mul_of_pos_left hm hs
  have htariff : stopMass k * m - 4 < L - 2 * B := by nlinarith
  exact ⟨hgain.trans_le hg, htariff.trans_le hg⟩

end SortingAdversary.Continuous
