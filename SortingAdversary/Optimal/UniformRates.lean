import SortingAdversary.Optimal.CutoffBounds

/-!
# Rates of the concrete bounded stage selector

The cheap coefficient below is read from the actual evaluated parameter
table. All limits use the implemented selector and its proved caps. The
finite scalar reduction keeps the eventual cutoff and the signed price
budget explicit for the execution theorem that instantiates them.
-/

namespace SortingAdversary.Optimal.UniformAdversary

open Filter AsymptoticRates SignedPrice
open scoped Topology

/-- The cheap charge actually produced by the bounded parameter scan. -/
def selectedCheap (n : ℕ) : ℕ :=
  match (UniformStage.choose n).decision with
  | .fallback => 0
  | .accepted _ _ a => a.runtime.cheap

theorem selectedCheap_square (n : ℕ) : selectedCheap n ^ 2 ≤ Parameters.logCap n := by
  unfold selectedCheap
  cases h : (UniformStage.choose n).decision with
  | fallback => simp
  | accepted j hj a => exact a.cheap_square

theorem selectedCheap_ratio_tendsto :
    Tendsto (fun n => (selectedCheap n : ℝ) / Real.log n) atTop (𝓝 0) := by
  apply cheap_log_ratio_tendsto
  · exact Eventually.of_forall (fun n => Nat.cast_nonneg _)
  · exact Eventually.of_forall (fun n => by exact_mod_cast selectedCheap_square n)

noncomputable def overhead (n : ℕ) : ℝ :=
  12 * stageTolerance (UniformStage.selectedStage n)

noncomputable def remainderFraction (n : ℕ) : ℝ :=
  terminalFraction n + 2 * ((selectedCheap n : ℝ) / Real.log n) +
    1 / (UniformStage.selectedStage n : ℝ) +
    priceCoefficient (Real.exp 1 * 128) *
      entropyEnvelope (12 / (UniformStage.selectedStage n : ℝ)) 256

theorem overhead_tendsto : Tendsto overhead atTop (𝓝 0) := by
  have h := (inverse_stage_tendsto UniformStage.selectedStage_tendsto (12 : ℝ)).div_const 100
  simp only [zero_div] at h
  apply h.congr'
  exact Eventually.of_forall (fun n => by unfold overhead stageTolerance; ring)

theorem remainderFraction_tendsto : Tendsto remainderFraction atTop (𝓝 0) := by
  have hc := selectedCheap_ratio_tendsto.const_mul (2 : ℝ)
  have hs := inverse_stage_tendsto UniformStage.selectedStage_tendsto 1
  have hp := (entropyEnvelope_tendsto_zero
    (inverse_stage_tendsto UniformStage.selectedStage_tendsto 12) 256).const_mul
      (priceCoefficient (Real.exp 1 * 128))
  change Tendsto (fun n => remainderFraction n) atTop (𝓝 0)
  simpa only [remainderFraction, mul_zero, add_zero] using
    ((terminalFraction_tendsto.add hc).add hs).add hp

theorem cheap_cast_eq {cap j : ℕ} (a : UniformStage.Accepted cap j) :
    (a.runtime.cheap : ℝ) = (a.controller.repair.scale.width.cheapCharge : ℝ) := by
  rw [a.runtime.cheap_eq]
  simp only [UniformStage.Accepted.controller, UniformStage.controllerParameters,
    WidthRepair.WidthParameters.cheapCharge, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem cut_log_le {cap j : ℕ} (a : UniformStage.Accepted cap j)
    (hj : 0 < j) :
    Real.log (a.controller.repair.scale.width.cutCharge : ℝ) ≤
      -Real.log (1 - stageTolerance j) := by
  let L : ℝ := a.runtime.normalizer.scale.width.L
  let A : ℝ := 2 * 4 ^ a.runtime.normalizer.scale.width.B
  have hA : 0 < A := by dsimp [A]; positivity
  have hAL : A < L := by
    dsimp [A, L]
    exact_mod_cast a.runtime.normalizer.scale.width.cutBudget
  have hL : 0 < L := hA.trans hAL
  have he : A / L ≤ stageTolerance j := by
    have h := a.cut_error
    rw [a.accuracy] at h
    have hc : (((2 * 4 ^ a.runtime.normalizer.scale.width.B : ℚ) /
        a.runtime.normalizer.scale.width.L : ℚ) : ℝ) ≤
        ((1 / (100 * (j : ℚ)) : ℚ) : ℝ) := by exact_mod_cast h
    simpa only [A, L, stageTolerance, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_one] using hc
  have hsmall := (stageTolerance_bounds hj).2
  have hpos : 0 < 1 - stageTolerance j := by linarith
  have hden : 0 < 1 - A / L := by
    have hlt : A / L < 1 := (div_lt_one hL).mpr hAL
    linarith
  have hc : (a.controller.repair.scale.width.cutCharge : ℝ) = 1 / (1 - A / L) := by
    simp only [UniformStage.Accepted.controller, UniformStage.controllerParameters,
      WidthRepair.WidthParameters.cutCharge, WidthRepair.WidthParameters.constant]
    push_cast
    change L / (L - A) = _
    field_simp
  rw [hc, Real.log_div (by norm_num) hden.ne', Real.log_one, zero_sub]
  exact neg_le_neg (Real.log_le_log hpos (by linarith))

/-- The degree, path and scale counts have an explicit inverse-stage bound
under the implemented physical clock. -/
theorem expensive_mass_le {j B : ℕ} (hj : 0 < j)
    {T q degree path scale : ℝ} (hT : 0 ≤ T)
    (hdegree : 0 ≤ degree) (hpath : 0 ≤ path) (hscale : 0 ≤ scale)
    (hq : q ≤ 4 * T)
    (hd : (j + 4 : ℝ) * degree ≤ 2 * q)
    (hp : path * Real.log (stagePathLength j) ≤ T)
    (hs : scale * Real.log ((stageScaleLength j B : ℝ) / 2) ≤ T) :
    degree + path + scale ≤ (12 / (j : ℝ)) * T := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hjdegree : (j : ℝ) * degree ≤ 8 * T := by nlinarith
  have hjpath : (j : ℝ) * path ≤ 2 * T := by
    rw [log_stagePathLength] at hp
    have h := mul_le_mul_of_nonneg_left half_le_log_two
      (mul_nonneg hjpos.le hpath)
    nlinarith
  have hjscale : (j : ℝ) * scale ≤ 2 * T := by
    have hl := inverse_scale_log_le hj B
    have hsp := stageScale_log_pos hj B
    have hsc : scale ≤ T / Real.log ((stageScaleLength j B : ℝ) / 2) :=
      (le_div_iff₀ hsp).mpr hs
    have h := mul_le_mul_of_nonneg_left hl hT
    have hbound : scale ≤ T * (2 / (j : ℝ)) := by
      calc
        scale ≤ T / Real.log ((stageScaleLength j B : ℝ) / 2) := hsc
        _ = T * (1 / Real.log ((stageScaleLength j B : ℝ) / 2)) := by ring
        _ ≤ _ := h
    have hmul := mul_le_mul_of_nonneg_left hbound hjpos.le
    have he : (j : ℝ) * (T * (2 / (j : ℝ))) = 2 * T := by field_simp
    rw [he] at hmul
    exact hmul
  rw [show (12 : ℝ) / j * T = 12 * T / j by ring]
  apply (le_div_iff₀ hjpos).mpr
  change (degree + path + scale) * (j : ℝ) ≤ 12 * T
  nlinarith

/-- Homogeneity and monotonicity convert the actual expensive-pin count
and capacity budget into the single explicit vanishing envelope. -/
theorem envelope_scaled_le {T X budget : ℝ} {j : ℕ}
    (hT : 0 < T) (hj : 0 < j) (hX : 0 ≤ X) (hbudget : 0 ≤ budget)
    (hXcap : X ≤ (12 / (j : ℝ)) * T) (hcap : budget ≤ 256 * T) :
    entropyEnvelope X budget ≤
      T * entropyEnvelope (12 / (j : ℝ)) 256 := by
  have hratio : X / T ≤ 12 / (j : ℝ) := (div_le_iff₀ hT).mpr hXcap
  have hbudgetratio : budget / T ≤ 256 := (div_le_iff₀ hT).mpr hcap
  have h := (entropyEnvelope_mono_budget (div_nonneg hX hT.le)
    (div_nonneg hbudget hT.le) hbudgetratio).trans
      (entropyEnvelope_mono_mass (div_nonneg hX hT.le) hratio (by norm_num))
  rw [← entropyEnvelope_div _ _ _ hT.ne'] at h
  have hs := (div_le_iff₀ hT).mp h
  simpa only [mul_comm] using hs

end SortingAdversary.Optimal.UniformAdversary
