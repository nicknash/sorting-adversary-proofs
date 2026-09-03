import SortingAdversary.StrengthenedCurvature.EndpointReduction
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Convexity of the endpoint quotient

The apparent singularity in `rho` is removed by the integral identity used in
the note.  This representation is also the clean route to sign-separated
convexity.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open intervalIntegral Set

/-- The elementary logarithmic remainder identity used below equation (52). -/
theorem sub_log_one_add_eq_integral {u : ℝ} (hu : -1 < u) :
    u - Real.log (1 + u) =
      u ^ 2 * ∫ z in (0 : ℝ)..1, z / (1 + u * z) := by
  by_cases hu0 : u = 0
  · simp [hu0]
  have hden (z : ℝ) (hz : z ∈ Set.uIcc (0 : ℝ) 1) : 1 + u * z ≠ 0 := by
    have hz' : 0 ≤ z ∧ z ≤ 1 := by simpa [Set.uIcc_of_le zero_le_one] using hz
    have hpos : 0 < 1 + u * z := by
      by_cases hupos : 0 ≤ u
      · have huz : 0 ≤ u * z := mul_nonneg hupos hz'.1
        linarith
      · have huz : u ≤ u * z := by
          have hp : 0 ≤ u * (z - 1) :=
            mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hupos) (by linarith)
          nlinarith
        linarith
    exact hpos.ne'
  let F : ℝ → ℝ := fun z =>
    (u * z - Real.log (1 + u * z)) / u ^ 2
  have hderiv (z : ℝ) (hz : z ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt F (z / (1 + u * z)) z := by
    have hlin : HasDerivAt (fun w : ℝ => 1 + u * w) u z := by
      simpa [mul_comm] using ((hasDerivAt_id (x := z)).mul_const u).const_add 1
    have hlog := hlin.log (hden z hz)
    have hnum := ((hasDerivAt_id (x := z)).mul_const u).sub hlog
    have hquot := hnum.div_const (u ^ 2)
    have hcoef : (1 * u - u / (1 + u * z)) / u ^ 2 =
        z / (1 + u * z) := by
      field_simp [hu0, hden z hz]
      ring
    have hd := hquot.congr_deriv hcoef
    simpa [F, mul_comm] using hd
  have hint : IntervalIntegrable (fun z : ℝ => z / (1 + u * z))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := aesop)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  change (∫ z in (0 : ℝ)..1, z / (1 + u * z)) = F 1 - F 0 at hfund
  rw [hfund]
  simp [F]
  field_simp [hu0]

/-- Integral form of the continuously extended quotient. -/
noncomputable def rhoIntegral (delta a b lambda x : ℝ) : ℝ :=
  let tp := delta + a
  let tm := b - delta
  lambda * ((2 * a / (1 + tp ^ 2)) * x +
      3 * a ^ 2 * ∫ z in (0 : ℝ)..1, z / (1 + a * x * z)) +
    (1 - lambda) * ((-2 * b / (1 + tm ^ 2)) * x +
      3 * b ^ 2 * ∫ z in (0 : ℝ)..1, z / (1 - b * x * z))

theorem rho_eq_rhoIntegral {delta a b lambda x : ℝ}
    (hplus : -1 < a * x) (hminus : b * x < 1) :
    rho delta a b lambda x = rhoIntegral delta a b lambda x := by
  by_cases hx : x = 0
  · subst x
    simp [rho, rhoIntegral, integral_id]
    ring
  · have hp := sub_log_one_add_eq_integral hplus
    have hm := sub_log_one_add_eq_integral (u := -b * x) (by linarith)
    have hm' : -b * x - Real.log (1 - b * x) =
        (b * x) ^ 2 * ∫ z in (0 : ℝ)..1, z / (1 - b * x * z) := by
      convert hm using 1 <;> ring
    rw [rho, if_neg hx]
    unfold phiAverage phiPlus phiMinus rhoIntegral
    dsimp only
    rw [hp, hm']
    field_simp [hx]

private theorem convexOn_mul_id (D : Set ℝ) (hD : Convex ℝ D) (c : ℝ) :
    ConvexOn ℝ D (fun x => c * x) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy p q hp hq hpq
  simp only [smul_eq_mul]
  rw [show c * (p * x + q * y) = p * (c * x) + q * (c * y) by ring]

private theorem convexOn_reciprocal_affine (D : Set ℝ) (hD : Convex ℝ D)
    (c : ℝ) (hden : ∀ x ∈ D, 0 < 1 + c * x) :
    ConvexOn ℝ D (fun x => (1 + c * x)⁻¹) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy p q hp hq hpq
  simp only [smul_eq_mul]
  let X := 1 + c * x
  let Y := 1 + c * y
  let Z := 1 + c * (p * x + q * y)
  have hX : 0 < X := hden x hx
  have hY : 0 < Y := hden y hy
  have hZ : 0 < Z := hden _ (hD hx hy hp hq hpq)
  have hZeq : Z = p * X + q * Y := by
    dsimp [X, Y, Z]
    nlinarith
  have hid : p * X⁻¹ + q * Y⁻¹ - Z⁻¹ =
      p * q * (X - Y) ^ 2 / (X * Y * Z) := by
    field_simp [hX.ne', hY.ne', hZ.ne']
    rw [hZeq]
    have hqeq : q = 1 - p := by linarith
    rw [hqeq]
    ring
  rw [show (1 + c * (p * x + q * y))⁻¹ = Z⁻¹ by rfl,
    show (1 + c * x)⁻¹ = X⁻¹ by rfl,
    show (1 + c * y)⁻¹ = Y⁻¹ by rfl]
  rw [← sub_nonneg]
  rw [hid]
  positivity

private theorem convexOn_integral_reciprocal (D : Set ℝ) (hD : Convex ℝ D)
    (c : ℝ) (hden : ∀ x ∈ D, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      0 < 1 + c * x * z) :
    ConvexOn ℝ D (fun x =>
      ∫ z in (0 : ℝ)..1, z / (1 + c * x * z)) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy p q hp hq hpq
  simp only [smul_eq_mul]
  have hconv (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      ConvexOn ℝ D (fun w => z / (1 + c * w * z)) := by
    have hrecip := convexOn_reciprocal_affine D hD (c * z) (by
      intro w hw
      convert hden w hw z hz using 1 <;> ring)
    have hz0 : 0 ≤ z := hz.1
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hrecip.smul hz0
  have hint (w : ℝ) (hw : w ∈ D) :
      IntervalIntegrable (fun z : ℝ => z / (1 + c * w * z))
        MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div₀ continuousOn_id
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro z hz
    exact (hden w hw z (by simpa [Set.uIcc_of_le zero_le_one] using hz)).ne'
  have hleft := hint _ (hD hx hy hp hq hpq)
  have hright : IntervalIntegrable
      (fun z : ℝ => p * (z / (1 + c * x * z)) +
        q * (z / (1 + c * y * z))) MeasureTheory.volume 0 1 :=
    (hint x hx).const_mul p |>.add ((hint y hy).const_mul q)
  have hmono := intervalIntegral.integral_mono_on zero_le_one hleft hright
    (fun z hz => (hconv z hz).2 hx hy hp hq hpq)
  rw [intervalIntegral.integral_add ((hint x hx).const_mul p)
      ((hint y hy).const_mul q),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  exact hmono

private theorem abs_mul_three_lt_one {c x z : ℝ}
    (hc : |c| < 1) (hx : |x| ≤ 1) (hz : |z| ≤ 1) :
    |c * x * z| < 1 := by
  rw [abs_mul, abs_mul]
  calc
    |c| * |x| * |z| ≤ |c| * |x| * 1 :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ |c| * 1 := by
      simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    _ = |c| := by ring
    _ < 1 := hc

private theorem one_add_mul_three_pos {c x z : ℝ}
    (hc : |c| < 1) (hx : |x| ≤ 1) (hz : |z| ≤ 1) :
    0 < 1 + c * x * z := by
  linarith [neg_lt_of_abs_lt (abs_mul_three_lt_one hc hx hz)]

/-- The endpoint quotient is convex throughout `[-1,1]`; the positive and
negative sign intervals used by the note are restrictions of this theorem. -/
theorem rho_convexOn_unitInterval {delta a b lambda : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (rho delta a b lambda) := by
  let D := Set.Icc (-1 : ℝ) 1
  have hD : Convex ℝ D := convex_Icc _ _
  have hinta : ConvexOn ℝ D (fun x =>
      ∫ z in (0 : ℝ)..1, z / (1 + a * x * z)) := by
    apply convexOn_integral_reciprocal D hD a
    intro x hx z hz
    apply one_add_mul_three_pos
    · rw [abs_of_nonneg ha0]
      exact ha1
    · exact (abs_le).2 hx
    · exact (abs_le).2 ⟨by linarith [hz.1], hz.2⟩
  have hintb : ConvexOn ℝ D (fun x =>
      ∫ z in (0 : ℝ)..1, z / (1 - b * x * z)) := by
    have h := convexOn_integral_reciprocal D hD (-b) (by
      intro x hx z hz
      convert one_add_mul_three_pos (c := -b) (x := x) (z := z)
        (by simpa [abs_of_nonneg hb0] using hb1)
        ((abs_le).2 hx) ((abs_le).2 ⟨by linarith [hz.1], hz.2⟩) using 1 <;> ring)
    simpa only [neg_mul, sub_eq_add_neg] using h
  have hplus : ConvexOn ℝ D (fun x =>
      (2 * a / (1 + (delta + a) ^ 2)) * x +
        3 * a ^ 2 * ∫ z in (0 : ℝ)..1, z / (1 + a * x * z)) :=
    (convexOn_mul_id D hD _).add (hinta.smul (by positivity))
  have hminus : ConvexOn ℝ D (fun x =>
      (-2 * b / (1 + (b - delta) ^ 2)) * x +
        3 * b ^ 2 * ∫ z in (0 : ℝ)..1, z / (1 - b * x * z)) :=
    (convexOn_mul_id D hD _).add (hintb.smul (by positivity))
  have havg := (hplus.smul hl0).add (hminus.smul (sub_nonneg.mpr hl1))
  have hintegral : ConvexOn ℝ D (rhoIntegral delta a b lambda) := by
    apply havg.congr
    intro w hw
    simp [rhoIntegral]
  apply hintegral.congr
  intro x hx
  symm
  apply rho_eq_rhoIntegral
  · have hxabs : |x| ≤ 1 := (abs_le).2 hx
    have hax : |a * x| < 1 := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc a * |x| ≤ a * 1 := mul_le_mul_of_nonneg_left hxabs ha0
        _ < 1 := by simpa using ha1
    linarith [neg_lt_of_abs_lt hax]
  · have hxabs : |x| ≤ 1 := (abs_le).2 hx
    have hbx : |b * x| < 1 := by
      rw [abs_mul, abs_of_nonneg hb0]
      calc b * |x| ≤ b * 1 := mul_le_mul_of_nonneg_left hxabs hb0
        _ < 1 := by simpa using hb1
    exact lt_of_le_of_lt (le_abs_self _) hbx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete sign-separated endpoint reduction (equation (54)), now with
the convexity hypotheses discharged. -/
theorem normalizedMotions_endpoint_reduction
    (motion : NormalizedMotions ι) (delta a b lambda : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (∑ i, phiAverage delta a b lambda (motion.alpha i)) ≤
      motion.positiveEnergy *
          positiveEndpointMax delta motion.positiveEnergy a b lambda +
        (1 - motion.positiveEnergy) *
          negativeEndpointMax delta motion.positiveEnergy a b lambda := by
  have hunit := rho_convexOn_unitInterval (delta := delta)
    ha0 ha1 hb0 hb1 hl0 hl1
  have hr0 := motion.positiveEnergy_nonneg
  have hr1 := motion.positiveEnergy_le_one
  have hP : Real.sqrt motion.positiveEnergy ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hr1
  have hN : Real.sqrt (1 - motion.positiveEnergy) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith [hr0]
  have hposconv : ConvexOn ℝ (Set.Icc 0 (Real.sqrt motion.positiveEnergy))
      (rho delta a b lambda) :=
    hunit.subset (by
      intro z hz
      exact ⟨by linarith [hz.1], hz.2.trans hP⟩) (convex_Icc _ _)
  have hnegconv : ConvexOn ℝ
      (Set.Icc (-Real.sqrt (1 - motion.positiveEnergy)) 0)
      (rho delta a b lambda) :=
    hunit.subset (by
      intro z hz
      exact ⟨(neg_le_neg hN).trans hz.1, by linarith [hz.2]⟩) (convex_Icc _ _)
  apply normalizedMotions_frame_reduction motion delta a b lambda
  · intro z hz0 hzP
    exact rho_le_positiveEndpointMax_of_convex hr0 hposconv hz0 hzP
  · intro z hzN hz0
    exact rho_le_negativeEndpointMax_of_convex hr1 hnegconv hzN hz0

/-- The coarser endpoint reduction used by the one-dimensional `7.361`
certificate.  It forgets the sign-energy split and keeps only
`∑ᵢ αᵢ² = 1`, so the whole frame is bounded by the two endpoints `±1`. -/
theorem normalizedMotions_unit_endpoint_reduction
    (motion : NormalizedMotions ι) (delta a b lambda : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (∑ i, phiAverage delta a b lambda (motion.alpha i)) ≤
      max (rho delta a b lambda (-1)) (rho delta a b lambda 1) := by
  let M := max (rho delta a b lambda (-1))
    (rho delta a b lambda 1)
  have hconv := rho_convexOn_unitInterval (delta := delta)
    ha0 ha1 hb0 hb1 hl0 hl1
  have halpha (i : ι) : motion.alpha i ∈ Set.Icc (-1 : ℝ) 1 := by
    have hsq : motion.alpha i ^ 2 ≤ 1 := by
      rw [← motion.energy_one]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (motion.alpha j))
        (Finset.mem_univ i)
    constructor <;> nlinarith [sq_nonneg (motion.alpha i - 1),
      sq_nonneg (motion.alpha i + 1)]
  have hpoint (i : ι) :
      phiAverage delta a b lambda (motion.alpha i) ≤
        motion.alpha i ^ 2 * M := by
    by_cases hi : motion.alpha i = 0
    · simp [hi]
    · rw [phiAverage_eq_rho_mul_sq hi, mul_comm]
      exact mul_le_mul_of_nonneg_left
        (hconv.le_max_of_mem_Icc (by simp) (by simp) (halpha i))
        (sq_nonneg _)
  calc
    (∑ i, phiAverage delta a b lambda (motion.alpha i)) ≤
        ∑ i, motion.alpha i ^ 2 * M :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = M := by rw [← Finset.sum_mul, motion.energy_one, one_mul]
    _ = max (rho delta a b lambda (-1))
        (rho delta a b lambda 1) := rfl

end StrengthenedCurvature
end SortingAdversary
