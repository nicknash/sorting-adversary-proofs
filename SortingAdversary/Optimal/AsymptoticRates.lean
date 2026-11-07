import SortingAdversary.Optimal.SignedPrice
import SortingAdversary.Optimal.Parameters
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Real.Sqrt

/-!
# Explicit vanishing rates for the uniform parameter schedule

The entropy envelope is continuous at zero despite its displayed division.
The terminal logarithmic remainder and the cheap-price square cap are proved
to vanish after normalization. Later results instantiate the stage scan and
the degree/path/scale choices with concrete inverse-stage bounds.

These are analytic and finite arithmetic results. They do not assume an
optimal-adversary theorem or assert a machine-time bound for an arbitrary
function supplied as the stage requirement.
-/

namespace SortingAdversary.Optimal.AsymptoticRates

open Filter
open scoped Topology BigOperators
open SignedPrice Parameters

theorem entropyEnvelope_tendsto_zero_at_zero (C : ℝ) :
    Tendsto (fun x : ℝ => entropyEnvelope x C) (𝓝 0) (𝓝 0) := by
  by_cases hC : C = 0
  · simpa [entropyEnvelope, hC] using
      (tendsto_id.mul_const (Real.log 2) :
        Tendsto (fun x : ℝ => x * Real.log 2) (𝓝 0) (𝓝 (0 * Real.log 2)))
  have hnum : Tendsto (fun x : ℝ => 2 * x + C) (𝓝 0) (𝓝 C) := by
    simpa using ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).const_mul (2 : ℝ)).add_const C
  have hfirst : Tendsto (fun x : ℝ => x * Real.log (2 * x + C)) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_id.mul (hnum.log hC)
  have hsecond : Tendsto (fun x : ℝ => x * Real.log x) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_mul_log.continuousAt :
      ContinuousAt (fun x : ℝ => x * Real.log x) 0).tendsto
  have hlimit := hfirst.sub hsecond
  simp only [sub_zero] at hlimit
  apply hlimit.congr'
  filter_upwards [hnum.eventually_ne hC] with x hx
  by_cases hxzero : x = 0
  · simp [hxzero, entropyEnvelope]
  have hratio : 2 + C / x = (2 * x + C) / x := by field_simp
  rw [entropyEnvelope, hratio, Real.log_div hx hxzero, mul_sub]

theorem entropyEnvelope_tendsto_zero {α : Type*} {l : Filter α} {mass : α → ℝ}
    (hmass : Tendsto mass l (𝓝 0)) (C : ℝ) :
    Tendsto (fun x => entropyEnvelope (mass x) C) l (𝓝 0) :=
  (entropyEnvelope_tendsto_zero_at_zero C).comp hmass

theorem entropyEnvelope_div (mass budget T : ℝ) (hT : T ≠ 0) :
    entropyEnvelope mass budget / T = entropyEnvelope (mass / T) (budget / T) := by
  by_cases hm : mass = 0
  · simp [hm, entropyEnvelope]
  unfold entropyEnvelope
  have hratio : (budget / T) / (mass / T) = budget / mass := by field_simp
  rw [hratio]
  ring

/-- The global signed envelope is negligible whenever the actual expensive
pin fraction vanishes and the explicit capacity/entropy budget is bounded
by a constant multiple of the main entropy. -/
theorem normalized_entropyEnvelope_tendsto {α : Type*} {l : Filter α}
    (mass budget T : α → ℝ) (C : ℝ)
    (hT : ∀ᶠ x in l, 0 < T x)
    (hmass : ∀ᶠ x in l, 0 ≤ mass x)
    (hbudget : ∀ᶠ x in l, 0 ≤ budget x)
    (hcap : ∀ᶠ x in l, budget x / T x ≤ C)
    (hfraction : Tendsto (fun x => mass x / T x) l (𝓝 0)) :
    Tendsto (fun x => entropyEnvelope (mass x) (budget x) / T x) l (𝓝 0) := by
  apply squeeze_zero' _ _ (entropyEnvelope_tendsto_zero hfraction C)
  · filter_upwards [hT, hmass, hbudget] with x htx hmx hbx
    exact div_nonneg (entropyEnvelope_nonneg hmx hbx) htx.le
  · filter_upwards [hT, hmass, hbudget, hcap] with x htx hmx hbx hcx
    rw [entropyEnvelope_div _ _ _ htx.ne']
    exact entropyEnvelope_mono_budget (div_nonneg hmx htx.le) (div_nonneg hbx htx.le) hcx

theorem log_div_self_tendsto :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)

theorem log_affine_div_self_tendsto (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.log (a + b * x) / x) atTop (𝓝 0) := by
  have haffine : Tendsto (fun x : ℝ => a + b * x) atTop atTop :=
    tendsto_const_nhds.add_atTop (Tendsto.const_mul_atTop hb tendsto_id)
  have hbase := Real.tendsto_pow_log_div_mul_add_atTop (1 / b) (-a / b) 1
    (one_div_ne_zero hb.ne')
  apply (hbase.comp haffine).congr'
  apply Eventually.of_forall
  intro x
  simp only [Function.comp_apply, pow_one]
  congr 1
  field_simp
  ring

theorem log_nat_succ_tendsto :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => (1 : ℝ) + n) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  exact Real.tendsto_log_atTop.comp (by simpa [add_comm] using hnat)

theorem log_nat_tendsto : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- This covers `n log(e(1+O(log n))) / (n log n)` after cancellation. -/
theorem terminal_log_ratio_tendsto (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.log (a + b * Real.log ((n : ℝ) + 1)) /
      Real.log ((n : ℝ) + 1)) atTop (𝓝 0) :=
  (log_affine_div_self_tendsto a b hb).comp log_nat_succ_tendsto

/-- The square cap, rather than merely a linear cap, makes the cheap
per-daughter constant negligible. -/
theorem square_cap_ratio_tendsto {α : Type*} {l : Filter α}
    (cheap budget : α → ℝ) (hbudget : Tendsto budget l atTop)
    (hcheap : ∀ᶠ x in l, 0 ≤ cheap x)
    (hsquare : ∀ᶠ x in l, cheap x ^ 2 ≤ budget x) :
    Tendsto (fun x => cheap x / budget x) l (𝓝 0) := by
  have hpositive : ∀ᶠ x in l, 0 < budget x := hbudget.eventually (eventually_gt_atTop 0)
  have hlim := (Real.tendsto_sqrt_atTop.comp hbudget).inv_tendsto_atTop
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hpositive, hcheap] with x hbx hcx
    exact div_nonneg hcx hbx.le
  · filter_upwards [hpositive, hcheap, hsquare] with x hbx hcx hsx
    have hroot := (Real.le_sqrt hcx hbx.le).mpr hsx
    have h := div_le_div_of_nonneg_right hroot hbx.le
    simpa only [Real.sqrt_div_self, Pi.inv_apply, Function.comp_apply] using h

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

theorem logCap_le_twice_log (n : ℕ) : (logCap n : ℝ) ≤ 2 * Real.log ((n : ℝ) + 1) := by
  have hpow := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  have hpowreal : (2 : ℝ) ^ logCap n ≤ (n : ℝ) + 1 := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ logCap n) hpowreal
  rw [Real.log_pow] at hlog
  have hlower := mul_le_mul_of_nonneg_left half_le_log_two (Nat.cast_nonneg (logCap n))
  nlinarith

/-- An accepted squared integer requirement under the actual logarithmic
stage cap pays only a vanishing normalized linear price. -/
theorem cheap_logCap_ratio_tendsto (cheap : ℕ → ℝ)
    (hcheap : ∀ᶠ n in atTop, 0 ≤ cheap n)
    (hsquare : ∀ᶠ n in atTop, cheap n ^ 2 ≤ logCap n) :
    Tendsto (fun n => cheap n / Real.log ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hcap : ∀ᶠ n in atTop, cheap n ^ 2 ≤ 2 * Real.log ((n : ℝ) + 1) := by
    filter_upwards [hsquare] with n hn
    exact hn.trans (logCap_le_twice_log n)
  have hbase := square_cap_ratio_tendsto cheap (fun n => 2 * Real.log ((n : ℝ) + 1))
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) log_nat_succ_tendsto) hcheap hcap
  have hscaled := hbase.const_mul (2 : ℝ)
  simp only [mul_zero] at hscaled
  apply hscaled.congr'
  filter_upwards [log_nat_succ_tendsto.eventually (eventually_gt_atTop 0)] with n hn
  field_simp

theorem log_succ_div_log_tendsto :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / Real.log n) atTop (𝓝 1) := by
  have hdiff := Real.tendsto_log_nat_add_one_sub_log.div_atTop log_nat_tendsto
  have hplus := hdiff.const_add 1
  simp only [add_zero] at hplus
  apply hplus.congr'
  filter_upwards [log_nat_tendsto.eventually (eventually_gt_atTop 0)] with n hn
  field_simp
  ring

theorem cheap_log_ratio_tendsto (cheap : ℕ → ℝ)
    (hcheap : ∀ᶠ n in atTop, 0 ≤ cheap n)
    (hsquare : ∀ᶠ n in atTop, cheap n ^ 2 ≤ logCap n) :
    Tendsto (fun n => cheap n / Real.log n) atTop (𝓝 0) := by
  have hproduct := (cheap_logCap_ratio_tendsto cheap hcheap hsquare).mul log_succ_div_log_tendsto
  simp only [zero_mul] at hproduct
  apply hproduct.congr'
  filter_upwards [log_nat_succ_tendsto.eventually (eventually_gt_atTop 0)] with n hn
  field_simp

/-! ## A concrete monotone stage scan -/

/-- Cumulative requirements make the forward scan valid even if a supplied
finite stage construction does not itself have monotone costs. Stage zero
is the fallback and has no requirement. -/
def requirementEnvelope (requirement : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => max (requirementEnvelope requirement j) (requirement (j + 1))

theorem requirementEnvelope_monotone (requirement : ℕ → ℕ) :
    Monotone (requirementEnvelope requirement) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_max_left _ _

theorem requirement_le_envelope (requirement : ℕ → ℕ) {j : ℕ} (hj : 0 < j) :
    requirement j ≤ requirementEnvelope requirement j := by
  cases j with
  | zero => omega
  | succ j => exact le_max_right _ _

def uniformStage (requirement : ℕ → ℕ) (n : ℕ) : ℕ :=
  logarithmicStage (requirementEnvelope requirement) n

theorem uniformStage_tendsto (requirement : ℕ → ℕ) :
    Tendsto (uniformStage requirement) atTop atTop :=
  logarithmicStage_tendsto (requirementEnvelope_monotone requirement)

theorem uniformStage_requirement_le (requirement : ℕ → ℕ) (n : ℕ)
    (hstage : 0 < uniformStage requirement n) :
    requirement (uniformStage requirement n) ≤ logCap n :=
  (requirement_le_envelope requirement hstage).trans
    (logarithmicStage_cost_le (by rfl : requirementEnvelope requirement 0 = 0) n)

/-- The actual uniform selector explicitly includes the square of the
cheap-price constant. `other` may contain the local-ball and arithmetic caps.
-/
def uniformRequirements (cheap other : ℕ → ℕ) (j : ℕ) : ℕ := max ((cheap j) ^ 2) (other j)

def uniformChoice (cheap other : ℕ → ℕ) : ℕ → ℕ := uniformStage (uniformRequirements cheap other)

theorem uniformChoice_tendsto (cheap other : ℕ → ℕ) :
    Tendsto (uniformChoice cheap other) atTop atTop := uniformStage_tendsto _

theorem uniformChoice_square_le (cheap other : ℕ → ℕ) (n : ℕ)
    (hstage : 0 < uniformChoice cheap other n) :
    (cheap (uniformChoice cheap other n)) ^ 2 ≤ logCap n := by
  have hreq := uniformStage_requirement_le (uniformRequirements cheap other) n hstage
  exact (le_max_left _ _).trans hreq

/-- No upper growth assumption on the cheap parameter is needed: the
computed stage cap itself proves the normalized cheap charge tends to zero.
-/
theorem uniform_cheap_ratio_tendsto (cheap other : ℕ → ℕ) :
    Tendsto (fun n => (cheap (uniformChoice cheap other n) : ℝ) / Real.log n) atTop (𝓝 0) := by
  apply cheap_log_ratio_tendsto
  · exact Eventually.of_forall (fun n => Nat.cast_nonneg _)
  · filter_upwards [(uniformChoice_tendsto cheap other).eventually (eventually_gt_atTop 0)] with n hn
    exact_mod_cast uniformChoice_square_le cheap other n hn

theorem inverse_stage_tendsto {stage : ℕ → ℕ} (hstage : Tendsto stage atTop atTop) (C : ℝ) :
    Tendsto (fun n => C / (stage n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hstage)

/-! ## Explicit degree, path, and scale choices -/

def stageDegree (j : ℕ) : ℕ := j + 4
def stagePathLength (j : ℕ) : ℕ := 2 ^ j
def stageScaleExponent (j B : ℕ) : ℕ := j * (B + 2) ^ 2
def stageScaleLength (j B : ℕ) : ℕ := 2 ^ stageScaleExponent j B

noncomputable def stageScaleSurcharge (B : ℕ) : ℝ := (1 + 2 * B : ℝ) * Real.log 2

theorem log_stagePathLength (j : ℕ) : Real.log (stagePathLength j : ℝ) = j * Real.log 2 := by
  simp [stagePathLength, Real.log_pow]

theorem log_stageScaleLength_half (j B : ℕ) :
    Real.log ((stageScaleLength j B : ℝ) / 2) =
      ((stageScaleExponent j B : ℝ) - 1) * Real.log 2 := by
  have hpos : 0 < stageScaleLength j B := Nat.two_pow_pos _
  have hne : (stageScaleLength j B : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Real.log_div hne (by norm_num)]
  simp only [stageScaleLength, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring

theorem stageScaleExponent_lower {j : ℕ} (hj : 0 < j) (B : ℕ) :
    j * (1 + 2 * B) + 1 ≤ stageScaleExponent j B := by
  have hpoly : 1 + 2 * B + 1 ≤ (B + 2) ^ 2 := by nlinarith [Nat.zero_le (B ^ 2)]
  have hmul := Nat.mul_le_mul_left j hpoly
  unfold stageScaleExponent
  nlinarith

theorem stageScale_log_lower {j : ℕ} (hj : 0 < j) (B : ℕ) :
    (j : ℝ) * stageScaleSurcharge B ≤ Real.log ((stageScaleLength j B : ℝ) / 2) := by
  have h := stageScaleExponent_lower hj B
  have hr : (j : ℝ) * (1 + 2 * B : ℝ) + 1 ≤ stageScaleExponent j B := by exact_mod_cast h
  rw [log_stageScaleLength_half, stageScaleSurcharge]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hr hlog]

theorem stageScale_log_pos {j : ℕ} (hj : 0 < j) (B : ℕ) :
    0 < Real.log ((stageScaleLength j B : ℝ) / 2) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hS : 0 < stageScaleSurcharge B := by
    unfold stageScaleSurcharge
    exact mul_pos (by positivity) (Real.log_pos (by norm_num))
  exact (mul_pos hjr hS).trans_le (stageScale_log_lower hj B)

theorem inverse_scale_log_le {j : ℕ} (hj : 0 < j) (B : ℕ) :
    1 / Real.log ((stageScaleLength j B : ℝ) / 2) ≤ 2 / (j : ℝ) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hS : (1 / 2 : ℝ) ≤ stageScaleSurcharge B := by
    unfold stageScaleSurcharge
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    nlinarith [half_le_log_two, mul_nonneg hB (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  have hlog := stageScale_log_lower hj B
  apply (div_le_div_iff₀ (stageScale_log_pos hj B) hjr).mpr
  nlinarith [mul_le_mul_of_nonneg_left hS hjr.le]

theorem scale_surcharge_ratio_le {j : ℕ} (hj : 0 < j) (B : ℕ) :
    stageScaleSurcharge B / Real.log ((stageScaleLength j B : ℝ) / 2) ≤ 1 / (j : ℝ) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  apply (div_le_div_iff₀ (stageScale_log_pos hj B) hjr).mpr
  simpa [mul_comm] using stageScale_log_lower hj B

/-- The regular budget after using the manuscript's clock cap
`q ≤ 2*n*log₂ n`, expressed as a fraction of `n*log n`. -/
noncomputable def regularFraction (j : ℕ) : ℝ :=
  4 / ((j + 3 : ℝ) * Real.log 2) + 1 / ((j : ℝ) * Real.log 2)

theorem regularFraction_le {j : ℕ} (hj : 0 < j) : regularFraction j ≤ 10 / (j : ℝ) := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfirst : 4 / ((j + 3 : ℝ) * Real.log 2) ≤ 8 / (j : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos (by positivity) hlog) hjr).mpr
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two (show 0 ≤ (j + 3 : ℝ) by positivity)]
  have hsecond : 1 / ((j : ℝ) * Real.log 2) ≤ 2 / (j : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hjr hlog) hjr).mpr
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two hjr.le]
  unfold regularFraction
  calc
    _ ≤ 8 / (j : ℝ) + 2 / (j : ℝ) := add_le_add hfirst hsecond
    _ = _ := by ring

noncomputable def expensiveFraction (j B : ℕ) : ℝ :=
  regularFraction j + 1 / Real.log ((stageScaleLength j B : ℝ) / 2)

theorem expensiveFraction_nonneg {j : ℕ} (hj : 0 < j) (B : ℕ) : 0 ≤ expensiveFraction j B := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale := stageScale_log_pos hj B
  unfold expensiveFraction regularFraction
  positivity

theorem expensiveFraction_le {j : ℕ} (hj : 0 < j) (B : ℕ) :
    expensiveFraction j B ≤ 12 / (j : ℝ) := by
  have hregular := regularFraction_le hj
  have hscale := inverse_scale_log_le hj B
  unfold expensiveFraction
  calc
    _ ≤ 10 / (j : ℝ) + 2 / (j : ℝ) := add_le_add hregular hscale
    _ = _ := by ring

theorem expensiveFraction_tendsto {stage : ℕ → ℕ} (hstage : Tendsto stage atTop atTop) (B : ℕ → ℕ) :
    Tendsto (fun n => expensiveFraction (stage n) (B (stage n))) atTop (𝓝 0) := by
  have hpositive : ∀ᶠ n in atTop, 0 < stage n := hstage.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' _ _ (inverse_stage_tendsto hstage 12)
  · filter_upwards [hpositive] with n hn
    exact expensiveFraction_nonneg hn _
  · filter_upwards [hpositive] with n hn
    exact expensiveFraction_le hn _

theorem scale_surcharge_ratio_tendsto {stage : ℕ → ℕ} (hstage : Tendsto stage atTop atTop)
    (B : ℕ → ℕ) :
    Tendsto (fun n => stageScaleSurcharge (B (stage n)) /
      Real.log ((stageScaleLength (stage n) (B (stage n)) : ℝ) / 2)) atTop (𝓝 0) := by
  have hpositive : ∀ᶠ n in atTop, 0 < stage n := hstage.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' _ _ (inverse_stage_tendsto hstage 1)
  · filter_upwards [hpositive] with n hn
    apply div_nonneg _ (stageScale_log_pos hn _).le
    unfold stageScaleSurcharge
    exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  · filter_upwards [hpositive] with n hn
    exact scale_surcharge_ratio_le hn _

/-! ## Physical losses and a fully explicit remainder rate -/

theorem neg_log_one_sub_le_twice (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hrewrite : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [hrewrite] at hlog
  have hratio : x / (1 - x) ≤ 2 * x := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  exact hlog.trans hratio

theorem physical_log_price_le (η : ℝ) (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) :
    -Real.log (1 / 2 - η) ≤ Real.log 2 + 4 * η := by
  have hpos : 0 < 1 - 2 * η := by linarith
  have h := neg_log_one_sub_le_twice (2 * η) (by linarith) (by linarith)
  rw [show (1 / 2 : ℝ) - η = (1 - 2 * η) / 2 by ring,
    Real.log_div hpos.ne' (by norm_num)]
  linarith

/-- One physical branch and at most one steep-cut charge per old physical
row have this explicit coefficient, before conversion to comparison bits. -/
theorem physical_and_cut_log_price_le (η : ℝ) (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) :
    -Real.log (1 / 2 - η) - Real.log (1 - η) ≤ Real.log 2 + 6 * η := by
  have hphysical := physical_log_price_le η hη hsmall
  have hcut := neg_log_one_sub_le_twice η hη (by linarith)
  linarith

theorem physical_and_cut_relative_le (η : ℝ) (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) :
    (-Real.log (1 / 2 - η) - Real.log (1 - η)) / Real.log 2 ≤ 1 + 12 * η := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  have hprice := physical_and_cut_log_price_le η hη hsmall
  nlinarith [mul_le_mul_of_nonneg_left half_le_log_two hη]

noncomputable def stageTolerance (j : ℕ) : ℝ := 1 / (100 * (j : ℝ))

theorem stageTolerance_bounds {j : ℕ} (hj : 0 < j) :
    0 ≤ stageTolerance j ∧ stageTolerance j ≤ 1 / 4 := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold stageTolerance
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * j)).mpr
    linarith

/-- After two type-specific codes are combined, the actual tree and
incidence bounds give this fixed normalized budget. The generous constant
256 is independent of every parameter stage. -/
theorem two_type_budget_le (T n P X K : ℝ) (hT : 0 ≤ T) (hX : 0 ≤ X)
    (hn : n ≤ 2 * T) (hP : P ≤ 8 * T) (hXcap : X ≤ 8 * T) (hK : K ≤ 8 * (n + P)) :
    2 * K + 2 * T + 2 * P + X * Real.log 8 ≤ 256 * T := by
  have hlog : Real.log 8 ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at h
    exact h
  have hmul := mul_le_mul_of_nonneg_left hlog hX
  nlinarith

noncomputable def terminalFraction (n : ℕ) : ℝ :=
  (1 + Real.log (9 + 64 * Real.log ((n : ℝ) + 1))) / Real.log n

theorem terminalFraction_tendsto : Tendsto terminalFraction atTop (𝓝 0) := by
  have hlog := (terminal_log_ratio_tendsto 9 64 (by norm_num)).mul log_succ_div_log_tendsto
  simp only [zero_mul] at hlog
  have hlog' : Tendsto (fun n : ℕ => Real.log (9 + 64 * Real.log ((n : ℝ) + 1)) /
      Real.log n) atTop (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [log_nat_succ_tendsto.eventually (eventually_gt_atTop 0)] with n hn
    field_simp
  have hone : Tendsto (fun n : ℕ => 1 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_nat_tendsto
  change Tendsto (fun n => terminalFraction n) atTop (𝓝 0)
  simpa only [terminalFraction, add_div, add_zero] using hone.add hlog'

/-- An explicit upper bound for the normalized non-comparison remainder.
The regular window factor is `8*16 = 128`; using that factor for both coded
types is conservative. The separate scale surcharge contributes `1/stage`.
-/
noncomputable def uniformRemainderFraction (cheap other : ℕ → ℕ) (n : ℕ) : ℝ :=
  let j := uniformChoice cheap other n
  terminalFraction n + 2 * ((cheap j : ℝ) / Real.log n) + 1 / (j : ℝ) +
    priceCoefficient (Real.exp 1 * 128) * entropyEnvelope (12 / (j : ℝ)) 256

theorem uniformRemainderFraction_tendsto (cheap other : ℕ → ℕ) :
    Tendsto (uniformRemainderFraction cheap other) atTop (𝓝 0) := by
  have hj := uniformChoice_tendsto cheap other
  have hcheap := (uniform_cheap_ratio_tendsto cheap other).const_mul (2 : ℝ)
  have hscale := inverse_stage_tendsto hj 1
  have hcalibrated := (entropyEnvelope_tendsto_zero (inverse_stage_tendsto hj 12) 256).const_mul
    (priceCoefficient (Real.exp 1 * 128))
  have h := ((terminalFraction_tendsto.add hcheap).add hscale).add hcalibrated
  change Tendsto (fun n => uniformRemainderFraction cheap other n) atTop (𝓝 0)
  simpa only [uniformRemainderFraction, mul_zero, add_zero] using h

noncomputable def uniformOverhead (cheap other : ℕ → ℕ) (n : ℕ) : ℝ :=
  12 * stageTolerance (uniformChoice cheap other n)

theorem uniformOverhead_tendsto (cheap other : ℕ → ℕ) :
    Tendsto (uniformOverhead cheap other) atTop (𝓝 0) := by
  have h := (inverse_stage_tendsto (uniformChoice_tendsto cheap other) (12 : ℝ)).div_const 100
  simp only [zero_div] at h
  apply h.congr'
  exact Eventually.of_forall (fun n => by unfold uniformOverhead stageTolerance; ring)

end SortingAdversary.Optimal.AsymptoticRates
