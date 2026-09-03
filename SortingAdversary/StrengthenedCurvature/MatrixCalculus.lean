import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# One-variable matrix calculus

Mathlib has the algebraic coefficient identity for
`det (I + X M)`.  This file combines it with entrywise differentiation to
derive Jacobi's formula for arbitrary finite real matrix curves.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

set_option maxHeartbeats 800000

open scoped BigOperators Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entrywise directional derivative of the Leibniz determinant sum. -/
noncomputable def detDifferential (A B : Matrix ι ι ℝ) : ℝ :=
  ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ •
    ∑ i : ι, (∏ j ∈ (Finset.univ.erase i), A (σ j) j) * B (σ i) i

theorem hasDerivAt_det_of_entrywise {M : ℝ → Matrix ι ι ℝ}
    {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) :
    HasDerivAt (fun t => (M t).det) (detDifferential (M s) M') s := by
  simp only [Matrix.det_apply, detDifferential]
  have hσ (σ : Equiv.Perm ι) :
      HasDerivAt (fun t => Equiv.Perm.sign σ • ∏ i, M t (σ i) i)
        (Equiv.Perm.sign σ •
          ∑ i, (∏ j ∈ (Finset.univ.erase i), M s (σ j) j) * M' (σ i) i) s := by
    apply HasDerivAt.const_smul
    have hp := HasDerivAt.finsetProd
      (u := (Finset.univ : Finset ι))
      (f := fun i t => M t (σ i) i)
      (f' := fun i => M' (σ i) i)
      (fun i _ => hM (σ i) i)
    have hfun : (∏ i : ι, fun t => M t (σ i) i) =
        (fun t => ∏ i : ι, M t (σ i) i) := by
      funext t
      exact Finset.prod_apply t Finset.univ (fun i t => M t (σ i) i)
    rw [hfun] at hp
    simpa only [smul_eq_mul] using hp
  have hs := HasDerivAt.sum (u := (Finset.univ : Finset (Equiv.Perm ι)))
    (fun σ _ => hσ σ)
  have hfun :
      (∑ σ : Equiv.Perm ι,
        fun t => Equiv.Perm.sign σ • ∏ i, M t (σ i) i) =
      (fun t => ∑ σ : Equiv.Perm ι,
        Equiv.Perm.sign σ • ∏ i, M t (σ i) i) := by
    funext t
    exact Finset.sum_apply t Finset.univ
      (fun σ t => Equiv.Perm.sign σ • ∏ i, M t (σ i) i)
  rw [hfun] at hs
  exact hs

theorem hasDerivAt_det_one_add_smul (C : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • C).det) C.trace 0 := by
  let p : Polynomial ℝ :=
    (1 + (Polynomial.X : Polynomial ℝ) •
      C.map (Polynomial.C : ℝ →+* Polynomial ℝ)).det
  have hp := p.hasDerivAt (0 : ℝ)
  have hderiv : p.derivative.eval (0 : ℝ) = C.trace := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul C
  rw [hderiv] at hp
  have hcurve : (fun t : ℝ => (1 + t • C).det) =
      (fun t : ℝ => Polynomial.eval t p) := by
    funext t
    symm
    simp only [p]
    rw [eval_det]
    apply congrArg Matrix.det
    ext i j
    rw [matPolyEquiv_eval]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul]
    by_cases hij : i = j
    · simp only [hij, if_pos, Polynomial.eval_one]
    · simp only [hij, if_false, Polynomial.eval_zero, zero_add, add_zero]
  rw [hcurve]
  exact hp

/-- Jacobi's formula for the determinant differential. -/
theorem detDifferential_eq_det_mul_trace (A B : Matrix ι ι ℝ)
    (hA : IsUnit A.det) :
    detDifferential A B = A.det * (A⁻¹ * B).trace := by
  have hleft : HasDerivAt (fun t : ℝ => (A + t • B).det)
      (detDifferential A B) 0 := by
    have hentry : ∀ i j, HasDerivAt
        (fun t : ℝ => (A + t • B) i j) (B i j) 0 := by
      intro i j
      simpa [add_comm] using
        ((hasDerivAt_id (x := (0 : ℝ))).mul_const (B i j)).const_add (A i j)
    simpa only [zero_smul, add_zero] using
      (hasDerivAt_det_of_entrywise
        (M := fun t : ℝ => A + t • B) (M' := B) (s := 0) hentry)
  have hAunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  have hfactor (t : ℝ) :
      (A + t • B).det = A.det * (1 + t • (A⁻¹ * B)).det := by
    have hmul : A * (1 + t • (A⁻¹ * B)) = A + t • B := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
        ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hA]
      simp
    rw [← hmul, Matrix.det_mul]
  have hright : HasDerivAt (fun t : ℝ => (A + t • B).det)
      (A.det * (A⁻¹ * B).trace) 0 := by
    have hc := (hasDerivAt_det_one_add_smul (A⁻¹ * B)).const_mul A.det
    have hfun : (fun t : ℝ => A.det * (1 + t • (A⁻¹ * B)).det) =
        (fun t : ℝ => (A + t • B).det) := by
      funext t
      exact (hfactor t).symm
    rw [hfun] at hc
    exact hc
  exact (hright.unique hleft).symm

/-- Jacobi's formula along an entrywise differentiable matrix curve. -/
theorem hasDerivAt_det {M : ℝ → Matrix ι ι ℝ}
    {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (hunit : IsUnit (M s).det) :
    HasDerivAt (fun t => (M t).det)
      ((M s).det * ((M s)⁻¹ * M').trace) s := by
  rw [← detDifferential_eq_det_mul_trace (M s) M' hunit]
  exact hasDerivAt_det_of_entrywise hM

/-- Log-determinant form of Jacobi's formula. -/
theorem hasDerivAt_log_det {M : ℝ → Matrix ι ι ℝ}
    {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (hdet : 0 < (M s).det) :
    HasDerivAt (fun t => Real.log (M t).det) (((M s)⁻¹ * M').trace) s := by
  have hdetCurve := hasDerivAt_det hM (isUnit_iff_ne_zero.mpr hdet.ne')
  have h := hdetCurve.log hdet.ne'
  have hcoef : ((M s).det * ((M s)⁻¹ * M').trace) / (M s).det =
      ((M s)⁻¹ * M').trace := by
    rw [mul_div_cancel_left₀ _ hdet.ne']
  rw [hcoef] at h
  exact h

/-- Nonsingular matrix inversion differentiated entrywise.  This formulation
avoids choosing one of the several norm structures available on finite
matrices: differentiability is established from the adjugate formula, and the
derivative is identified by differentiating `M M⁻¹ = I` in a neighborhood of
the nonsingular point. -/
theorem differentiableAt_nonsingInv_entry {M : ℝ → Matrix ι ι ℝ}
    {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (hdet : (M s).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) s := by
  have hdetCurve := hasDerivAt_det_of_entrywise hM
  have hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) s := by
    rw [show (fun t => (M t).adjugate i j) =
        (fun t => ((M t).updateRow j (Pi.single i 1)).det) by
      funext t
      exact Matrix.adjugate_apply (M t) i j]
    apply (hasDerivAt_det_of_entrywise
      (M := fun t => (M t).updateRow j (Pi.single i 1))
      (M' := (M' : Matrix ι ι ℝ).updateRow j 0) (s := s) ?_).differentiableAt
    intro u v
    by_cases hu : u = j
    · subst u
      simp only [Matrix.updateRow_self, Pi.zero_apply]
      exact hasDerivAt_const (x := s) (c := Pi.single i 1 v)
    · simpa only [Matrix.updateRow_ne hu] using hM u v
  rw [show (fun t => (M t)⁻¹ i j) =
      (fun t => ((M t).det)⁻¹ * (M t).adjugate i j) by
    funext t
    simp [Matrix.inv_def, Ring.inverse_eq_inv]]
  exact hdetCurve.differentiableAt.inv hdet |>.mul hadj

/-- The entrywise derivative formula `(M⁻¹)' = -M⁻¹ M' M⁻¹`. -/
theorem hasDerivAt_nonsingInv_entry {M : ℝ → Matrix ι ι ℝ}
    {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (hunit : IsUnit (M s).det) (i j : ι) :
    HasDerivAt (fun t => (M t)⁻¹ i j)
      ((-((M s)⁻¹ * M' * (M s)⁻¹)) i j) s := by
  let N' : Matrix ι ι ℝ := fun u v => deriv (fun t => (M t)⁻¹ u v) s
  have hN' (u v : ι) : HasDerivAt (fun t => (M t)⁻¹ u v) (N' u v) s :=
    (differentiableAt_nonsingInv_entry hM
      (isUnit_iff_ne_zero.mp hunit) u v).hasDerivAt
  have hdetCurve := hasDerivAt_det_of_entrywise hM
  have hnear : ∀ᶠ t in nhds s, (M t).det ≠ 0 :=
    hdetCurve.continuousAt.eventually_ne (isUnit_iff_ne_zero.mp hunit)
  have hmatrix : M' * (M s)⁻¹ + M s * N' = 0 := by
    ext u v
    have hprod : HasDerivAt (fun t => (M t * (M t)⁻¹) u v)
        ((M' * (M s)⁻¹ + M s * N') u v) s := by
      have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ι))
        (fun k _ => (hM u k).mul (hN' k v))
      have hfun :
          (∑ k : ι, (fun t => M t u k) * fun t => (M t)⁻¹ k v) =
            (fun t => ∑ k : ι, M t u k * (M t)⁻¹ k v) := by
        funext t
        exact Finset.sum_apply t Finset.univ
          (fun k t => M t u k * (M t)⁻¹ k v)
      rw [hfun] at hsum
      simpa only [Matrix.mul_apply, Matrix.add_apply,
        Finset.sum_add_distrib] using hsum
    have heq : (fun _ : ℝ => (1 : Matrix ι ι ℝ) u v) =ᶠ[nhds s]
        (fun t => (M t * (M t)⁻¹) u v) := by
      filter_upwards [hnear] with t ht
      have hm := Matrix.mul_nonsing_inv (M t) (isUnit_iff_ne_zero.mpr ht)
      exact (congrArg (fun A : Matrix ι ι ℝ => A u v) hm).symm
    have hzero : HasDerivAt (fun t => (M t * (M t)⁻¹) u v) 0 s :=
      (hasDerivAt_const (x := s) (c := (1 : Matrix ι ι ℝ) u v)).congr_of_eventuallyEq
        heq.symm
    exact hprod.unique hzero
  have hMN : M s * N' = -(M' * (M s)⁻¹) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hmatrix
  have hInv : (M s)⁻¹ * M s = (1 : Matrix ι ι ℝ) :=
    Matrix.nonsing_inv_mul _ hunit
  have hN'eq : N' = -((M s)⁻¹ * M' * (M s)⁻¹) := by
    calc
      N' = (1 : Matrix ι ι ℝ) * N' := by simp
      _ = ((M s)⁻¹ * M s) * N' := by rw [hInv]
      _ = (M s)⁻¹ * (M s * N') := by rw [Matrix.mul_assoc]
      _ = (M s)⁻¹ * (-(M' * (M s)⁻¹)) := by rw [hMN]
      _ = -((M s)⁻¹ * M' * (M s)⁻¹) := by noncomm_ring
  rw [← hN'eq]
  exact hN' i j

/-- Jacobi's first-derivative expression along a matrix curve. -/
noncomputable def logDetFirstDerivative
    (M M1 : ℝ → Matrix ι ι ℝ) (t : ℝ) : ℝ :=
  ((M t)⁻¹ * M1 t).trace

/-- Derivative of the Jacobi expression.  Together with
`hasDerivAt_log_det`, this is the second-derivative formula

`(log det M)'' = tr (-M⁻¹ M' M⁻¹ M' + M⁻¹ M'')`.
-/
theorem hasDerivAt_logDetFirstDerivative {M M1 : ℝ → Matrix ι ι ℝ}
    {M' M'' : Matrix ι ι ℝ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (hM1 : ∀ i j, HasDerivAt (fun t => M1 t i j) (M'' i j) s)
    (hvalue : M1 s = M') (hunit : IsUnit (M s).det) :
    HasDerivAt (fun t => logDetFirstDerivative M M1 t)
      ((-((M s)⁻¹ * M' * (M s)⁻¹) * M' + (M s)⁻¹ * M'').trace) s := by
  have hinv (i j : ι) := hasDerivAt_nonsingInv_entry hM hunit i j
  have hdiag (i : ι) : HasDerivAt
      (fun t => ((M t)⁻¹ * M1 t) i i)
      ((-((M s)⁻¹ * M' * (M s)⁻¹) * M' + (M s)⁻¹ * M'') i i) s := by
    have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ι))
      (fun k _ => (hinv i k).mul (hM1 k i))
    have hfun :
        (∑ k : ι, (fun t => (M t)⁻¹ i k) * fun t => M1 t k i) =
          (fun t => ∑ k : ι, (M t)⁻¹ i k * M1 t k i) := by
      funext t
      exact Finset.sum_apply t Finset.univ
        (fun k t => (M t)⁻¹ i k * M1 t k i)
    rw [hfun] at hsum
    simpa only [Matrix.mul_apply, Matrix.add_apply, hvalue,
      Finset.sum_add_distrib] using hsum
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ι))
    (fun i _ => hdiag i)
  have hfun :
      (∑ i : ι, fun t => ((M t)⁻¹ * M1 t) i i) =
        (fun t => ((M t)⁻¹ * M1 t).trace) := by
    funext t
    rw [Finset.sum_apply]
    rfl
  rw [hfun] at hsum
  simpa only [logDetFirstDerivative, Matrix.trace, Matrix.diag_apply] using hsum

end StrengthenedCurvature
end SortingAdversary
