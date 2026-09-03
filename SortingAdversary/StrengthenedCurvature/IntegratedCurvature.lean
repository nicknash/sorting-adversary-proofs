import SortingAdversary.StrengthenedCurvature.LocalGeometry
import SortingAdversary.StrengthenedCurvature.RhoConvexity
import Mathlib.Analysis.Convex.Deriv

/-!
# Twice-integrated curvature comparison

This module packages the analytic integration step without appealing to an
informal Taylor expansion.  A second-derivative majorant is converted to the
required endpoint inequality by convexity of the difference.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open Set
open scoped BigOperators

-- Keep the scalar module used by the one-dimensional derivative API fixed.
-- Several equivalent `Module ℝ ℝ` instances are available through the matrix
-- imports, and fixing this one avoids an irrelevant instance diamond.
local instance realModule : Module ℝ ℝ := Semiring.toModule

/-- If `g'' ≥ f''` on `[0,a]`, the tangent-normalized increment of `f` is
bounded by that of `g`. -/
theorem endpoint_sub_tangent_le_of_secondDeriv_le
    {f f' f'' g g' g'' : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo (0 : ℝ) a, HasDerivAt f' (f'' x) x)
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Ioo (0 : ℝ) a, HasDerivAt g' (g'' x) x)
    (hsecond : ∀ x ∈ Set.Ioo (0 : ℝ) a, f'' x ≤ g'' x) :
    f a - f 0 - a * f' 0 ≤ g a - g 0 - a * g' 0 := by
  let H : ℝ → ℝ := fun x => g x - f x
  let H' : ℝ → ℝ := fun x => g' x - f' x
  let H'' : ℝ → ℝ := fun x => g'' x - f'' x
  have hcont : ContinuousOn H (Set.Icc (0 : ℝ) a) := by
    intro x hx
    exact ((hg x hx).sub (hf x hx)).continuousAt.continuousWithinAt
  have hH : ∀ x ∈ interior (Set.Icc (0 : ℝ) a),
      HasDerivWithinAt H (H' x) (interior (Set.Icc (0 : ℝ) a)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) a := by simpa [interior_Icc] using hx
    exact ((hg x ⟨hx'.1.le, hx'.2.le⟩).sub
      (hf x ⟨hx'.1.le, hx'.2.le⟩)).hasDerivWithinAt
  have hH' : ∀ x ∈ interior (Set.Icc (0 : ℝ) a),
      HasDerivWithinAt H' (H'' x) (interior (Set.Icc (0 : ℝ) a)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) a := by simpa [interior_Icc] using hx
    exact ((hg' x hx').sub (hf' x hx')).hasDerivWithinAt
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) a) H :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hcont hH hH'
      (by
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) a := by simpa [interior_Icc] using hx
        exact sub_nonneg.mpr (hsecond x hx'))
  have hslope := hconv.le_slope_of_hasDerivAt (x := 0) (y := a)
    (by simp [ha.le]) (by simp [ha.le]) ha
    ((hg 0 ⟨le_rfl, ha.le⟩).sub (hf 0 ⟨le_rfl, ha.le⟩))
  rw [slope_def_field] at hslope
  simp only [H, H', sub_zero] at hslope
  have hslope' := (le_div_iff₀ ha).mp hslope
  nlinarith [hslope']

/-- The elementary primitive whose second derivative is the old-row term
`3α²/(1+sα)²`. -/
noncomputable def rowCurvaturePrimitive (alpha s : ℝ) : ℝ :=
  3 * (s * alpha - Real.log (1 + s * alpha))

noncomputable def rowCurvaturePrimitive' (alpha s : ℝ) : ℝ :=
  3 * (alpha - alpha / (1 + s * alpha))

noncomputable def rowCurvaturePrimitive'' (alpha s : ℝ) : ℝ :=
  3 * alpha ^ 2 / (1 + s * alpha) ^ 2

theorem hasDerivAt_rowCurvaturePrimitive (alpha s : ℝ)
    (hden : 1 + s * alpha ≠ 0) :
    HasDerivAt (rowCurvaturePrimitive alpha)
      (rowCurvaturePrimitive' alpha s) s := by
  have hlin : HasDerivAt (fun t : ℝ => 1 + t * alpha) alpha s := by
    simpa using ((hasDerivAt_id (x := s)).mul_const alpha).const_add 1
  have hlog := hlin.log hden
  change HasDerivAt (fun t : ℝ =>
    3 * (t * alpha - Real.log (1 + t * alpha)))
      (3 * (alpha - alpha / (1 + s * alpha))) s
  convert! (((hasDerivAt_id (x := s)).mul_const alpha).sub hlog).const_smul
    (3 : ℝ) using 1 <;> simp

theorem hasDerivAt_rowCurvaturePrimitive' (alpha s : ℝ)
    (hden : 1 + s * alpha ≠ 0) :
    HasDerivAt (rowCurvaturePrimitive' alpha)
      (rowCurvaturePrimitive'' alpha s) s := by
  have hlin : HasDerivAt (fun t : ℝ => 1 + t * alpha) alpha s := by
    simpa using ((hasDerivAt_id (x := s)).mul_const alpha).const_add 1
  have hinv := hlin.inv hden
  have hterm := hinv.const_mul alpha
  have hdiff := (hasDerivAt_const (x := s) (c := alpha)).sub hterm
  have hscaled := hdiff.const_mul 3
  apply hscaled.congr_deriv
  simp only [rowCurvaturePrimitive'']
  field_simp [hden]
  ring

@[simp] theorem rowCurvaturePrimitive_zero (alpha : ℝ) :
    rowCurvaturePrimitive alpha 0 = 0 := by
  simp [rowCurvaturePrimitive]

@[simp] theorem rowCurvaturePrimitive'_zero (alpha : ℝ) :
    rowCurvaturePrimitive' alpha 0 = 0 := by
  simp [rowCurvaturePrimitive']

section FiniteFrame

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]
  [DecidableEq ρ] [DecidableEq κ]

/-- Sum of the elementary row primitives over a finite row frame. -/
noncomputable def rowCurvatureSum (d : ρ → ℝ) : ℝ → ℝ :=
  ∑ i, rowCurvaturePrimitive (d i)

noncomputable def rowCurvatureSum' (d : ρ → ℝ) : ℝ → ℝ :=
  ∑ i, rowCurvaturePrimitive' (d i)

noncomputable def rowCurvatureSum'' (d : ρ → ℝ) : ℝ → ℝ :=
  ∑ i, rowCurvaturePrimitive'' (d i)

theorem hasDerivAt_rowCurvatureSum (d : ρ → ℝ) (s : ℝ)
    (hden : ∀ i, rowDenominator d s i ≠ 0) :
    HasDerivAt (rowCurvatureSum d) (rowCurvatureSum' d s) s := by
  unfold rowCurvatureSum rowCurvatureSum'
  simpa only [Finset.sum_apply] using
    HasDerivAt.sum (u := (Finset.univ : Finset ρ))
      (fun i _ => hasDerivAt_rowCurvaturePrimitive (d i) s (hden i))

theorem hasDerivAt_rowCurvatureSum' (d : ρ → ℝ) (s : ℝ)
    (hden : ∀ i, rowDenominator d s i ≠ 0) :
    HasDerivAt (rowCurvatureSum' d) (rowCurvatureSum'' d s) s := by
  unfold rowCurvatureSum' rowCurvatureSum''
  simpa only [Finset.sum_apply] using
    HasDerivAt.sum (u := (Finset.univ : Finset ρ))
      (fun i _ => hasDerivAt_rowCurvaturePrimitive' (d i) s (hden i))

@[simp] theorem rowCurvatureSum_zero (d : ρ → ℝ) :
    rowCurvatureSum d 0 = 0 := by
  simp [rowCurvatureSum]

@[simp] theorem rowCurvatureSum'_zero (d : ρ → ℝ) :
    rowCurvatureSum' d 0 = 0 := by
  simp [rowCurvatureSum']

theorem rowCurvatureSum''_eq_scaledRate (d : ρ → ℝ) (s : ℝ) :
    rowCurvatureSum'' d s = 3 * ∑ i, scaledRate d s i ^ 2 := by
  rw [rowCurvatureSum'', Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rowCurvaturePrimitive'', scaledRate, rowDenominator]
  rw [div_pow]
  ring

/-- Twice integration of the dimension-free curvature inequality.  This is
the rigorous form of equation (32) before the value and first derivative at
the origin are substituted. -/
theorem scaledLogDet_endpoint_sub_tangent_le
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) {a : ℝ} (ha : 0 < a)
    (hden : ∀ s ∈ Set.Icc (0 : ℝ) a, ∀ i, rowDenominator d s i ≠ 0)
    (hdet : ∀ s ∈ Set.Icc (0 : ℝ) a, 0 < (scaledGram V d s).det) :
    scaledLogDet V d a - scaledLogDet V d 0 -
        a * scaledLogDetFirst V d 0 ≤ rowCurvatureSum d a := by
  have hmain := endpoint_sub_tangent_le_of_secondDeriv_le
    (f := scaledLogDet V d) (f' := scaledLogDetFirst V d)
    (f'' := scaledProjectionCurvature V d)
    (g := rowCurvatureSum d) (g' := rowCurvatureSum' d)
    (g'' := rowCurvatureSum'' d) ha
    (fun s hs => hasDerivAt_scaledLogDet V d s (hden s hs) (hdet s hs))
    (fun s hs => hasDerivAt_scaledLogDetFirst_projection V d s
      (hden s ⟨hs.1.le, hs.2.le⟩)
      (isUnit_iff_ne_zero.mpr (ne_of_gt (hdet s ⟨hs.1.le, hs.2.le⟩))))
    (fun s hs => hasDerivAt_rowCurvatureSum d s (hden s hs))
    (fun s hs => hasDerivAt_rowCurvatureSum' d s
      (hden s ⟨hs.1.le, hs.2.le⟩))
    (by
      intro s hs
      rw [rowCurvatureSum''_eq_scaledRate]
      have hcurv := scaledProjectionCurvature_upper V d s
        (isUnit_iff_ne_zero.mpr (ne_of_gt (hdet s ⟨hs.1.le, hs.2.le⟩)))
      exact hcurv.trans (sub_le_self _ (mul_nonneg (by norm_num) (sq_nonneg _))))
  simpa using hmain

end FiniteFrame

end StrengthenedCurvature
end SortingAdversary
