import SortingAdversary.StrengthenedCurvature.RateSaving

/-!
# Closed form for the crossover saving

This is Appendix A, equation (69), of the strengthened-curvature note.  It
is proved by differentiating the displayed elementary expression and using
the interval fundamental theorem of calculus.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open Set intervalIntegral

set_option maxHeartbeats 2000000

local instance crossRealModule : Module ℝ ℝ := Semiring.toModule

/-- Elementary closed form for one half of the crossover integral, with an
arbitrary certified cutoff `L`. -/
noncomputable def crossClosed (ell P N L : ℝ) : ℝ :=
  let U := 1 + P * L
  let V := 1 - N * L
  let T1 := (P * ell + 1) * (1 - U⁻¹) - Real.log U
  let T2 := (N * ell - 1) * (V⁻¹ - 1) - Real.log V
  let J1 := ((P * ell + 1) * Real.log U - (U - 1)) / P ^ 2
  let J2 := (-(N * ell - 1) * Real.log V + (1 - V)) / N ^ 2
  let J3 := P / (P + N) * J1 + N / (P + N) * J2
  (1 / 2 : ℝ) * (T1 + T2 - 2 * P * N * J3)

theorem crossClosed_zero (ell P N : ℝ) (hP : P ≠ 0) (hN : N ≠ 0) :
    crossClosed ell P N 0 = 0 := by
  simp [crossClosed, hP, hN]

theorem hasDerivAt_crossClosed (ell P N L : ℝ)
    (hP : 0 < P) (hN : 0 < N) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hN1 : N ≤ 1) :
    HasDerivAt (crossClosed ell P N)
      ((1 / 2 : ℝ) * crossIntegrand ell P N L) L := by
  have hU : 1 + P * L ≠ 0 := ne_of_gt (by positivity)
  have hVpos : 0 < 1 - N * L := by
    have hNL : N * L ≤ 1 * L := mul_le_mul_of_nonneg_right hN1 hL0
    linarith
  have hV : 1 - N * L ≠ 0 := hVpos.ne'
  have hV' : 1 - L * N ≠ 0 := by
    simpa [mul_comm] using hV
  have hUd : HasDerivAt (fun x : ℝ => 1 + P * x) P L := by
    simpa [mul_comm] using ((hasDerivAt_id (x := L)).mul_const P).const_add 1
  have hVd : HasDerivAt (fun x : ℝ => 1 - N * x) (-N) L := by
    simpa [sub_eq_add_neg, mul_comm] using
      ((hasDerivAt_id (x := L)).mul_const (-N)).const_add 1
  have hlogU := hUd.log hU
  have hlogV := hVd.log hV
  have hinvU := hUd.inv hU
  have hinvV := hVd.inv hV
  have hT1 := (((hasDerivAt_const (x := L) (c := (1 : ℝ))).sub hinvU).const_mul
    (P * ell + 1)).sub hlogU
  have hT2 := ((hinvV.sub (hasDerivAt_const (x := L) (c := (1 : ℝ)))).const_mul
    (N * ell - 1)).sub hlogV
  have hJ1 := ((hlogU.const_mul (P * ell + 1)).sub
    (hUd.sub (hasDerivAt_const (x := L) (c := (1 : ℝ))))).div_const (P ^ 2)
  have hJ2 := ((hlogV.const_mul (-(N * ell - 1))).add
    ((hasDerivAt_const (x := L) (c := (1 : ℝ))).sub hVd)).div_const (N ^ 2)
  have hJ3 := (hJ1.const_mul (P / (P + N))).add
    (hJ2.const_mul (N / (P + N)))
  have htotal := ((hT1.add hT2).sub (hJ3.const_mul (2 * P * N))).const_mul
    (1 / 2 : ℝ)
  unfold crossClosed crossIntegrand
  dsimp only
  apply htotal.congr_deriv
  field_simp [hP.ne', hN.ne', (add_pos hP hN).ne', hU, hV]
  field_simp [hV']
  ring

/-- Appendix A's closed form equals the defining integral. -/
theorem crossClosed_eq_integral (ell P N L : ℝ)
    (hP : 0 < P) (hN : 0 < N) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hN1 : N ≤ 1) :
    crossClosed ell P N L =
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..L, crossIntegrand ell P N s := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (crossClosed ell P N)
        ((1 / 2 : ℝ) * crossIntegrand ell P N s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL0] using hs
    exact hasDerivAt_crossClosed ell P N s hP hN hs'.1
      (lt_of_le_of_lt hs'.2 hL1) hN1
  have hint : IntervalIntegrable
      (fun s => (1 / 2 : ℝ) * crossIntegrand ell P N s)
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    unfold crossIntegrand
    apply (continuousOn_const.sub continuousOn_id).mul
    apply ContinuousOn.pow
    apply ContinuousOn.sub
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) L := by
        simpa [Set.uIcc_of_le hL0] using hs
      simpa only [Pi.add_apply, Pi.mul_apply, id_eq] using
        (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs'.1 hP.le)))
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) L := by
        simpa [Set.uIcc_of_le hL0] using hs
      have hNL : N * s ≤ 1 * s := mul_le_mul_of_nonneg_right hN1 hs'.1
      simpa only [Pi.sub_apply, Pi.mul_apply, id_eq] using
        (ne_of_gt (show 0 < 1 - s * N by
          linarith [lt_of_le_of_lt hs'.2 hL1]))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [crossClosed_zero ell P N hP.ne' hN.ne'] at hfund
  rw [intervalIntegral.integral_const_mul] at hfund
  linarith

/-- Scalar form of the continuity fact used for truncated crossover
integrals.  The hypotheses are exactly the domain conditions appearing in
the certificate. -/
theorem crossIntegrand_intervalIntegrable_of_le_one
    {a L P N : ℝ} (hL0 : 0 ≤ L) (hLa : L ≤ a) (ha1 : a < 1)
    (hP0 : 0 ≤ P) (hN0 : 0 ≤ N) (hN1 : N ≤ 1) :
    IntervalIntegrable (crossIntegrand a P N) MeasureTheory.volume 0 L := by
  apply ContinuousOn.intervalIntegrable
  unfold crossIntegrand
  apply (continuousOn_const.sub continuousOn_id).mul
  apply ContinuousOn.pow
  apply ContinuousOn.sub
  · apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL0] using hs
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hs'.1 hP0))
  · apply ContinuousOn.div continuousOn_const
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) L := by
      simpa [Set.uIcc_of_le hL0] using hs
    have hs1 : s < 1 := lt_of_le_of_lt (hs'.2.trans hLa) ha1
    have hsN : s * N ≤ s * 1 := mul_le_mul_of_nonneg_left hN1 hs'.1
    change 1 - s * N ≠ 0
    exact ne_of_gt (by linarith)

/-- Increasing positive energy and decreasing negative energy increases the
rational crossover gap pointwise. -/
theorem crossoverGap_mono
    {P₀ P N N₀ s : ℝ}
    (hP₀ : 0 ≤ P₀) (hP : P₀ ≤ P) (hN : 0 ≤ N) (hN₀ : N ≤ N₀)
    (hN₀one : N₀ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    P₀ / (1 + s * P₀) - N₀ / (1 - s * N₀) ≤
      P / (1 + s * P) - N / (1 - s * N) := by
  have hPnonneg : 0 ≤ P := hP₀.trans hP
  have hN₀nonneg : 0 ≤ N₀ := hN.trans hN₀
  have hdP₀ : 0 < 1 + s * P₀ := by positivity
  have hdP : 0 < 1 + s * P := by positivity
  have hsN₀ : s * N₀ < 1 := by
    have : s * N₀ ≤ s * 1 := mul_le_mul_of_nonneg_left hN₀one hs0
    linarith
  have hsN : s * N ≤ s * N₀ := mul_le_mul_of_nonneg_left hN₀ hs0
  have hdN₀ : 0 < 1 - s * N₀ := by linarith
  have hdN : 0 < 1 - s * N := by linarith
  have hpos : P₀ / (1 + s * P₀) ≤ P / (1 + s * P) := by
    apply (div_le_div_iff₀ hdP₀ hdP).2
    nlinarith
  have hneg : N / (1 - s * N) ≤ N₀ / (1 - s * N₀) := by
    apply (div_le_div_iff₀ hdN hdN₀).2
    nlinarith
  linarith

/-- The crossover gap is nonnegative up to its algebraic zero. -/
theorem crossoverGap_nonneg_before
    {P N s : ℝ} (hP : 0 < P) (hN : 0 < N) (hN1 : N ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hs : s ≤ (P - N) / (2 * P * N)) :
    0 ≤ P / (1 + s * P) - N / (1 - s * N) := by
  have hdP : 0 < 1 + s * P := by positivity
  have hsN : s * N ≤ s * 1 := mul_le_mul_of_nonneg_left hN1 hs0
  have hdN : 0 < 1 - s * N := by linarith
  have hprod : s * (2 * P * N) ≤ P - N :=
    (le_div_iff₀ (by positivity : 0 < 2 * P * N)).mp hs
  rw [sub_nonneg]
  apply (div_le_div_iff₀ hdN hdP).2
  nlinarith

/-- A closed-form crossover value at a lower endpoint bounds any larger
energy imbalance, larger displacement, and larger certified cutoff. -/
theorem crossClosed_le_crossIntegral
    {ell a P₀ P N N₀ L T : ℝ}
    (hP₀ : 0 < P₀) (hN₀pos : 0 < N₀) (hP : P₀ ≤ P)
    (hN : 0 ≤ N) (hNN₀ : N ≤ N₀) (hN₀one : N₀ ≤ 1)
    (hL0 : 0 ≤ L) (hLell : L ≤ ell) (hella : ell ≤ a)
    (ha1 : a < 1) (hLT : L ≤ T) (hTa : T ≤ a)
    (hcut : L ≤ (P₀ - N₀) / (2 * P₀ * N₀)) :
    crossClosed ell P₀ N₀ L ≤
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, crossIntegrand a P N s := by
  have hP0 : 0 ≤ P := hP₀.le.trans hP
  have hT0 : 0 ≤ T := hL0.trans hLT
  have hL1 : L < 1 := hLell.trans_lt (hella.trans_lt ha1)
  have hbaseline := crossIntegrand_intervalIntegrable_of_le_one
    hL0 hLell (hella.trans_lt ha1) hP₀.le hN₀pos.le hN₀one
  have hactualL := crossIntegrand_intervalIntegrable_of_le_one
    hL0 (hLell.trans hella) ha1 hP0 hN (hNN₀.trans hN₀one)
  have hactualT := crossIntegrand_intervalIntegrable_of_le_one
    hT0 hTa ha1 hP0 hN (hNN₀.trans hN₀one)
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) L,
      crossIntegrand ell P₀ N₀ s ≤ crossIntegrand a P N s := by
    intro s hs
    have hs1 : s < 1 := hs.2.trans_lt hL1
    have hg₀ := crossoverGap_nonneg_before hP₀ hN₀pos hN₀one hs.1 hs1
      (hs.2.trans hcut)
    have hgap := crossoverGap_mono hP₀.le hP hN hNN₀ hN₀one hs.1 hs1
    have hsq :
        (P₀ / (1 + s * P₀) - N₀ / (1 - s * N₀)) ^ 2 ≤
          (P / (1 + s * P) - N / (1 - s * N)) ^ 2 := by
      nlinarith
    unfold crossIntegrand
    have hw₀ : 0 ≤ ell - s := sub_nonneg.mpr (hs.2.trans hLell)
    have hw : ell - s ≤ a - s := by linarith
    have hwa : 0 ≤ a - s := hw₀.trans hw
    exact mul_le_mul hw hsq (sq_nonneg _) hwa
  have hsame : (∫ s in (0 : ℝ)..L, crossIntegrand ell P₀ N₀ s) ≤
      ∫ s in (0 : ℝ)..L, crossIntegrand a P N s :=
    intervalIntegral.integral_mono_on hL0 hbaseline hactualL hpoint
  have hextend : (∫ s in (0 : ℝ)..L, crossIntegrand a P N s) ≤
      ∫ s in (0 : ℝ)..T, crossIntegrand a P N s := by
    apply intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := T)
      le_rfl hL0 hLT
    · show ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T),
          (0 : ℝ) ≤ crossIntegrand a P N s
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (sub_nonneg.mpr (hs.2.trans hTa)) (sq_nonneg _)
    · exact hactualT
  rw [crossClosed_eq_integral ell P₀ N₀ L hP₀ hN₀pos hL0 hL1 hN₀one]
  exact mul_le_mul_of_nonneg_left (hsame.trans hextend) (by norm_num)

/-- The endpoint rule used by the finite certificate: on the side
`r > 1/2`, a closed-form value computed at the endpoint of an `r`-box and
with a lower displacement bounds the true saving everywhere in the box. -/
theorem crossClosed_le_gammaPlus_of_half_lt
    {ell a r₀ r L : ℝ}
    (hr₀half : 1 / 2 < r₀) (hr₀one : r₀ < 1)
    (hrr₀ : r₀ ≤ r) (hrone : r ≤ 1)
    (hL0 : 0 ≤ L) (hLell : L ≤ ell) (hella : ell ≤ a)
    (ha1 : a < 1)
    (hcut : L ≤
      (Real.sqrt r₀ - Real.sqrt (1 - r₀)) /
        (2 * Real.sqrt r₀ * Real.sqrt (1 - r₀))) :
    crossClosed ell (Real.sqrt r₀) (Real.sqrt (1 - r₀)) L ≤
      gammaPlus a r := by
  let P₀ := Real.sqrt r₀
  let N₀ := Real.sqrt (1 - r₀)
  let P := Real.sqrt r
  let N := Real.sqrt (1 - r)
  have hr₀0 : 0 < r₀ := by linarith
  have hr0 : 0 ≤ r := le_trans hr₀0.le hrr₀
  have h1r0 : 0 ≤ 1 - r := by linarith
  have h1r₀0 : 0 < 1 - r₀ := by linarith
  have hP₀pos : 0 < P₀ := by
    exact Real.sqrt_pos.2 hr₀0
  have hN₀pos : 0 < N₀ := by
    exact Real.sqrt_pos.2 h1r₀0
  have hPmono : P₀ ≤ P := by
    exact Real.sqrt_le_sqrt hrr₀
  have hNmono : N ≤ N₀ := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN₀one : N₀ ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  have hPN : N < P := by
    exact Real.sqrt_lt_sqrt h1r0 (by linarith)
  have hL1 : L < 1 := hLell.trans_lt (hella.trans_lt ha1)
  rw [gammaPlus]
  dsimp only
  rw [if_neg (not_le_of_gt hPN)]
  by_cases hNzero : N = 0
  · rw [if_pos hNzero]
    exact crossClosed_le_crossIntegral hP₀pos hN₀pos hPmono hN0 hNmono
      hN₀one hL0 hLell hella ha1 (hLell.trans hella) le_rfl hcut
  · rw [if_neg hNzero]
    have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNzero)
    have hPpos : 0 < P := hNpos.trans hPN
    have hbaselineGap : 0 ≤
        P₀ / (1 + L * P₀) - N₀ / (1 - L * N₀) :=
      crossoverGap_nonneg_before hP₀pos hN₀pos hN₀one hL0 hL1 hcut
    have hactualGap : 0 ≤
        P / (1 + L * P) - N / (1 - L * N) :=
      hbaselineGap.trans
        (crossoverGap_mono hP₀pos.le hPmono hN0 hNmono hN₀one hL0 hL1)
    have hdP : 0 < 1 + L * P := by positivity
    have hLN : L * N ≤ L * N₀ := mul_le_mul_of_nonneg_left hNmono hL0
    have hLN₀ : L * N₀ < 1 := by
      have : L * N₀ ≤ L * 1 := mul_le_mul_of_nonneg_left hN₀one hL0
      linarith
    have hdN : 0 < 1 - L * N := by linarith
    have hprod : L * (2 * P * N) ≤ P - N := by
      rw [sub_nonneg] at hactualGap
      have hcross := (div_le_div_iff₀ hdN hdP).mp hactualGap
      nlinarith
    have hactualCut : L ≤ (P - N) / (2 * P * N) :=
      (le_div_iff₀ (by positivity : 0 < 2 * P * N)).2 hprod
    exact crossClosed_le_crossIntegral hP₀pos hN₀pos hPmono hN0 hNmono
      hN₀one hL0 hLell hella ha1
      (le_min (hLell.trans hella) hactualCut) (min_le_left _ _) hcut

/-- The constant-gap side of equation (41), evaluated at the endpoint of an
`r`-box closest to `1/2`. -/
theorem constantGap_le_gammaPlus_of_le_half
    {ell a r r₁ : ℝ} (hr0 : 0 ≤ r) (hrr₁ : r ≤ r₁)
    (hr₁half : r₁ ≤ 1 / 2) (hell0 : 0 ≤ ell) (hella : ell ≤ a) :
    ell ^ 2 / 4 * (Real.sqrt (1 - r₁) - Real.sqrt r₁) ^ 2 ≤
      gammaPlus a r := by
  have hr₁0 : 0 ≤ r₁ := hr0.trans hrr₁
  have hr1 : r ≤ 1 := by linarith
  have hdom : Real.sqrt r ≤ Real.sqrt (1 - r) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hPmono : Real.sqrt r ≤ Real.sqrt r₁ := Real.sqrt_le_sqrt hrr₁
  have hNmono : Real.sqrt (1 - r₁) ≤ Real.sqrt (1 - r) :=
    Real.sqrt_le_sqrt (by linarith)
  have hgap₁0 : 0 ≤ Real.sqrt (1 - r₁) - Real.sqrt r₁ := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hgap : Real.sqrt (1 - r₁) - Real.sqrt r₁ ≤
      Real.sqrt (1 - r) - Real.sqrt r := by linarith
  have ha0 : 0 ≤ a := hell0.trans hella
  rw [gammaPlus]
  dsimp only
  rw [if_pos hdom]
  have hsqa : ell ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hell0 ha0).2 hella
  have hsqgap : (Real.sqrt (1 - r₁) - Real.sqrt r₁) ^ 2 ≤
      (Real.sqrt (1 - r) - Real.sqrt r) ^ 2 :=
    (sq_le_sq₀ hgap₁0 (hgap₁0.trans hgap)).2 hgap
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hfirst : ell ^ 2 / 4 ≤ a ^ 2 / 4 := by
    exact div_le_div_of_nonneg_right hsqa hfour.le
  exact mul_le_mul hfirst hsqgap (sq_nonneg _) (div_nonneg (sq_nonneg _) hfour.le)

/-- Both strengthened-curvature savings are nonnegative. -/
theorem gammaPlus_nonneg {a r : ℝ} (ha0 : 0 ≤ a) : 0 ≤ gammaPlus a r := by
  let P := Real.sqrt r
  let N := Real.sqrt (1 - r)
  rw [gammaPlus]
  dsimp only
  by_cases hNP : N ≥ P
  · rw [if_pos hNP]
    positivity
  · rw [if_neg hNP]
    have hPN : N < P := lt_of_not_ge hNP
    by_cases hNzero : N = 0
    · rw [if_pos hNzero]
      apply mul_nonneg (by norm_num)
      apply intervalIntegral.integral_nonneg ha0
      intro s hs
      exact mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg _)
    · rw [if_neg hNzero]
      have hN0 : 0 ≤ N := Real.sqrt_nonneg _
      have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNzero)
      have hPpos : 0 < P := hNpos.trans hPN
      have hs0 : 0 ≤ (P - N) / (2 * P * N) := by positivity
      have hmin0 : 0 ≤ min a ((P - N) / (2 * P * N)) := le_min ha0 hs0
      apply mul_nonneg (by norm_num)
      apply intervalIntegral.integral_nonneg hmin0
      intro s hs
      exact mul_nonneg (sub_nonneg.mpr (hs.2.trans (min_le_left _ _))) (sq_nonneg _)

theorem gammaMinus_nonneg {b r : ℝ} (hb0 : 0 ≤ b) : 0 ≤ gammaMinus b r := by
  exact gammaPlus_nonneg hb0

end StrengthenedCurvature
end SortingAdversary
