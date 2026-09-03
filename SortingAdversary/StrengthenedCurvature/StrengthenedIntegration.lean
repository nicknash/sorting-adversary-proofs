import SortingAdversary.StrengthenedCurvature.IntegratedCurvature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integrating the sign-imbalance curvature saving

This file keeps the negative term in the strengthened second-derivative
estimate.  The basic identity is the integral-remainder formula

`f(a) - f(0) - a f'(0) = ∫ s in 0..a, (a-s) f''(s)`.

It is proved directly by integration by parts, so no informal Taylor
expansion enters the trusted proof.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

set_option maxHeartbeats 2000000

open Set intervalIntegral
open scoped BigOperators

-- Keep the scalar module used by the derivative API fixed (the matrix imports
-- provide an equivalent instance as well).
local instance strengthenedRealModule : Module ℝ ℝ := Semiring.toModule

private theorem continuousAt_finset_sum_real
    {X ι : Type*} [TopologicalSpace X] {x : X}
    (t : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ t, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ t, f i y) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) x)
  | @insert i t hi ih =>
      convert (hf i (Finset.mem_insert_self i t)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)) using 1
      funext y
      simp [Finset.sum_insert hi]

private theorem continuousAt_matrix_transpose
    {X m n : Type*} [TopologicalSpace X] {x : X}
    {A : X → Matrix m n ℝ} (hA : ContinuousAt A x) :
    ContinuousAt (fun y ↦ (A y).transpose) x := by
  exact continuous_id.matrix_transpose.continuousAt.comp hA

private theorem continuousAt_matrix_mul
    {X m n p : Type*} [TopologicalSpace X] [Fintype n] {x : X}
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) :
    ContinuousAt (fun y ↦ A y * B y) x := by
  exact (continuous_fst.matrix_mul continuous_snd).continuousAt.comp (hA.prodMk hB)

private theorem continuousAt_matrix_diagonal
    {X n : Type*} [TopologicalSpace X] [DecidableEq n] {x : X}
    {d : X → n → ℝ} (hd : ContinuousAt d x) :
    ContinuousAt (fun y ↦ Matrix.diagonal (d y)) x := by
  exact continuous_id.matrix_diagonal.continuousAt.comp hd

private theorem continuousAt_frobeniusSq
    {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n] {x : X}
    {A : X → Matrix n n ℝ} (hA : ContinuousAt A x) :
    ContinuousAt (fun y ↦ frobeniusSq (A y)) x := by
  unfold frobeniusSq
  exact continuousAt_finset_sum_real Finset.univ
    (fun i y ↦ ∑ j, A y i j ^ 2)
    (fun i _ ↦ continuousAt_finset_sum_real Finset.univ
      (fun j y ↦ A y i j ^ 2)
      (fun j _ ↦ ((continuous_apply_apply i j).continuousAt.comp hA).pow 2))

/-- The weighted second-derivative integral is the first-order Taylor
remainder. -/
theorem weighted_secondDeriv_integral_eq
    {f f' f'' : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt f' (f'' s) s)
    (hf''int : IntervalIntegrable f'' MeasureTheory.volume 0 a) :
    (∫ s in (0 : ℝ)..a, (a - s) * f'' s) =
      f a - f 0 - a * f' 0 := by
  have hf'cont : ContinuousOn f' (uIcc (0 : ℝ) a) := by
    simpa [uIcc_of_le ha] using HasDerivAt.continuousOn hf'
  have hf'int : IntervalIntegrable f' MeasureTheory.volume 0 a :=
    hf'cont.intervalIntegrable
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := a)
    (u := fun s : ℝ => a - s) (u' := fun _ => (-1 : ℝ))
    (v := f') (v' := f'')
    (fun s _ => by
      simpa [sub_eq_add_neg] using (hasDerivAt_neg s).const_add a)
    (fun s hs => hf' s (by simpa [uIcc_of_le ha] using hs))
    (intervalIntegrable_const)
    hf''int
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hf s (by simpa [uIcc_of_le ha] using hs)) hf'int
  calc
    (∫ s in (0 : ℝ)..a, (a - s) * f'' s) =
        (a - a) * f' a - (a - 0) * f' 0 -
          ∫ s in (0 : ℝ)..a, (-1 : ℝ) * f' s := hparts
    _ = f a - f 0 - a * f' 0 := by
      simp only [sub_self, zero_mul, sub_zero, neg_one_mul, integral_neg, hftc]
      ring

/-- A pointwise saving in a second-derivative majorant subtracts its weighted
integral from the endpoint bound. -/
theorem endpoint_sub_tangent_le_of_secondDeriv_le_sub
    {f f' f'' g g' g'' saving : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt f' (f'' s) s)
    (hg : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt g (g' s) s)
    (hg' : ∀ s ∈ Set.Icc (0 : ℝ) a, HasDerivAt g' (g'' s) s)
    (hf''int : IntervalIntegrable f'' MeasureTheory.volume 0 a)
    (hg''int : IntervalIntegrable g'' MeasureTheory.volume 0 a)
    (hsaving : ContinuousOn saving (Set.Icc (0 : ℝ) a))
    (hsecond : ∀ s ∈ Set.Icc (0 : ℝ) a, f'' s ≤ g'' s - saving s) :
    f a - f 0 - a * f' 0 ≤
      g a - g 0 - a * g' 0 -
        ∫ s in (0 : ℝ)..a, (a - s) * saving s := by
  have hscont : ContinuousOn saving (uIcc (0 : ℝ) a) := by
    simpa [uIcc_of_le ha] using hsaving
  have hsint : IntervalIntegrable saving MeasureTheory.volume 0 a :=
    hscont.intervalIntegrable
  have hleft : IntervalIntegrable (fun s => (a - s) * f'' s)
      MeasureTheory.volume 0 a :=
    hf''int.continuousOn_mul (by fun_prop)
  have hright : IntervalIntegrable (fun s => (a - s) * (g'' s - saving s))
      MeasureTheory.volume 0 a :=
    (hg''int.sub hsint).continuousOn_mul (by fun_prop)
  have hmono :
      (∫ s in (0 : ℝ)..a, (a - s) * f'' s) ≤
        ∫ s in (0 : ℝ)..a, (a - s) * (g'' s - saving s) := by
    apply intervalIntegral.integral_mono_on ha hleft hright
    intro s hs
    exact mul_le_mul_of_nonneg_left (hsecond s hs) (sub_nonneg.mpr hs.2)
  rw [weighted_secondDeriv_integral_eq ha hf hf' hf''int] at hmono
  have hsplit : (fun s : ℝ => (a - s) * (g'' s - saving s)) =
      (fun s => (a - s) * g'' s - (a - s) * saving s) := by
    funext s
    ring
  rw [hsplit, intervalIntegral.integral_sub
      (hg''int.continuousOn_mul (by fun_prop))
      (hsint.continuousOn_mul (by fun_prop)),
    weighted_secondDeriv_integral_eq ha hg hg' hg''int] at hmono
  exact hmono

/-- The signed-rate norm gap appearing in the projection curvature theorem. -/
noncomputable def scaledRateGap
    {ρ : Type*} [Fintype ρ]
    (d : ρ → ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (∑ i, positivePart (scaledRate d s i) ^ 2) -
    Real.sqrt (∑ i, negativePart (scaledRate d s i) ^ 2)

/-- The augmented logarithmic determinant bound with the sign saving retained. -/
theorem scaledLogDet_endpoint_sub_tangent_le_strengthened
    {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq ρ] [DecidableEq κ]
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) {a : ℝ} (ha : 0 < a)
    (hden : ∀ s ∈ Set.Icc (0 : ℝ) a, ∀ i, rowDenominator d s i ≠ 0)
    (hdet : ∀ s ∈ Set.Icc (0 : ℝ) a, 0 < (scaledGram V d s).det) :
    scaledLogDet V d a - scaledLogDet V d 0 -
        a * scaledLogDetFirst V d 0 ≤
      rowCurvatureSum d a -
        (1 / 2 : ℝ) *
          ∫ s in (0 : ℝ)..a, (a - s) * scaledRateGap d s ^ 2 := by
  let saving : ℝ → ℝ := fun s => (1 / 2 : ℝ) * scaledRateGap d s ^ 2
  have hrate (i : ρ) : ContinuousOn (fun s => scaledRate d s i)
      (Set.Icc (0 : ℝ) a) := by
    unfold scaledRate rowDenominator
    exact ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      (fun s hs => hden s hs i)
  have hsaving : ContinuousOn saving (Set.Icc (0 : ℝ) a) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.pow
    apply ContinuousOn.sub
    · apply ContinuousOn.sqrt
      · apply continuousOn_finsetSum Finset.univ
        intro i _
        apply ContinuousOn.pow
        exact continuous_max.comp_continuousOn ((hrate i).prodMk continuousOn_const)
    · apply ContinuousOn.sqrt
      · apply continuousOn_finsetSum Finset.univ
        intro i _
        apply ContinuousOn.pow
        exact continuous_max.comp_continuousOn ((hrate i).neg.prodMk continuousOn_const)
  have hf''cont : ContinuousOn (scaledProjectionCurvature V d)
      (Set.Icc (0 : ℝ) a) := by
    intro s hs
    have hrateAt (i : ρ) : ContinuousAt (fun u ↦ scaledRate d u i) s := by
      unfold scaledRate rowDenominator
      exact continuousAt_const.div
        (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
        (hden s hs i)
    have hrates : ContinuousAt (fun u ↦ scaledRate d u) s :=
      continuousAt_pi.mpr hrateAt
    have hrows : ContinuousAt (scaledRows V d) s := by
      change ContinuousAt (fun u i j ↦
        V i j / rowDenominator d u i) s
      exact continuousAt_pi.mpr fun i ↦ continuousAt_pi.mpr fun j ↦ by
        unfold rowDenominator
        exact continuousAt_const.div
          (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
          (hden s hs i)
    have hrowsT : ContinuousAt (fun u ↦ (scaledRows V d u).transpose) s :=
      continuousAt_matrix_transpose hrows
    have hgram : ContinuousAt (scaledGram V d) s := by
      unfold scaledGram columnGram
      exact continuousAt_matrix_mul hrowsT hrows
    have hinvMap : ContinuousAt
        (fun u => (scaledGram V d u)⁻¹) s := by
      apply (continuousAt_matrix_inv (scaledGram V d s) ?_).comp hgram
      rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv by
        funext x
        exact Ring.inverse_eq_inv x]
      exact continuousAt_inv₀ (ne_of_gt (hdet s hs))
    have hprojection : ContinuousAt
        (fun u => rowProjection (scaledRows V d u)) s := by
      unfold rowProjection columnGram
      exact continuousAt_matrix_mul (continuousAt_matrix_mul hrows hinvMap) hrowsT
    have hdiag : ContinuousAt
        (fun u => Matrix.diagonal (scaledRate d u)) s := by
      exact continuousAt_matrix_diagonal hrates
    have hratesq : ContinuousAt (fun u => ∑ i, scaledRate d u i ^ 2) s := by
      simpa using continuousAt_finset_sum_real Finset.univ
        (fun i u ↦ scaledRate d u i ^ 2) (fun i _ ↦ (hrateAt i).pow 2)
    have hPDP : ContinuousAt (fun u ↦
        rowProjection (scaledRows V d u) * Matrix.diagonal (scaledRate d u) *
          rowProjection (scaledRows V d u)) s :=
      continuousAt_matrix_mul (continuousAt_matrix_mul hprojection hdiag) hprojection
    have hcomplement : ContinuousAt (fun u ↦
        projectionComplement (rowProjection (scaledRows V d u))) s := by
      unfold projectionComplement
      exact continuousAt_const.sub hprojection
    have hQDQ : ContinuousAt (fun u ↦
        projectionComplement (rowProjection (scaledRows V d u)) *
          Matrix.diagonal (scaledRate d u) *
          projectionComplement (rowProjection (scaledRows V d u))) s :=
      continuousAt_matrix_mul (continuousAt_matrix_mul hcomplement hdiag) hcomplement
    unfold scaledProjectionCurvature
    dsimp only
    exact (((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (3 : ℝ)) s).mul hratesq).sub
      (continuousAt_frobeniusSq hPDP)).sub
        ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (3 : ℝ)) s).mul
          (continuousAt_frobeniusSq hQDQ)) |>.continuousWithinAt
  have hg''cont : ContinuousOn (rowCurvatureSum'' d)
      (Set.Icc (0 : ℝ) a) := by
    rw [show rowCurvatureSum'' d = fun s => 3 * ∑ i, scaledRate d s i ^ 2 by
      funext s
      exact rowCurvatureSum''_eq_scaledRate d s]
    exact continuousOn_const.mul
      (continuousOn_finsetSum Finset.univ fun i _ => (hrate i).pow 2)
  have hmain := endpoint_sub_tangent_le_of_secondDeriv_le_sub
    (f := scaledLogDet V d) (f' := scaledLogDetFirst V d)
    (f'' := scaledProjectionCurvature V d)
    (g := rowCurvatureSum d) (g' := rowCurvatureSum' d)
    (g'' := rowCurvatureSum'' d) (saving := saving) ha.le
    (fun s hs => hasDerivAt_scaledLogDet V d s (hden s hs) (hdet s hs))
    (fun s hs => hasDerivAt_scaledLogDetFirst_projection V d s
      (hden s hs) (isUnit_iff_ne_zero.mpr (ne_of_gt (hdet s hs))))
    (fun s hs => hasDerivAt_rowCurvatureSum d s (hden s hs))
    (fun s hs => hasDerivAt_rowCurvatureSum' d s (hden s hs))
    (by
      have hc : ContinuousOn (scaledProjectionCurvature V d)
          (uIcc (0 : ℝ) a) := by simpa [uIcc_of_le ha.le] using hf''cont
      exact hc.intervalIntegrable)
    (by
      have hc : ContinuousOn (rowCurvatureSum'' d)
          (uIcc (0 : ℝ) a) := by simpa [uIcc_of_le ha.le] using hg''cont
      exact hc.intervalIntegrable)
    hsaving
    (by
      intro s hs
      rw [rowCurvatureSum''_eq_scaledRate]
      simpa [saving, scaledRateGap] using
        (scaledProjectionCurvature_upper V d s
          (isUnit_iff_ne_zero.mpr (ne_of_gt (hdet s hs)))))
  simp only [rowCurvatureSum_zero, rowCurvatureSum'_zero, mul_zero,
    sub_zero, saving] at hmain
  have hfactor : (fun s : ℝ =>
      (a - s) * ((1 / 2 : ℝ) * scaledRateGap d s ^ 2)) =
      (fun s => (1 / 2 : ℝ) * ((a - s) * scaledRateGap d s ^ 2)) := by
    funext s
    ring
  rw [hfactor, intervalIntegral.integral_const_mul] at hmain
  simpa [mul_assoc] using hmain

end StrengthenedCurvature
end SortingAdversary
