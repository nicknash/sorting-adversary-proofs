import SortingAdversary.StrengthenedCurvature.MatrixCalculus
import SortingAdversary.StrengthenedCurvature.ProjectionCurvature
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing

/-!
# Curvature of an augmented row-scaled Gram matrix

This file connects the entrywise `log det` calculus to the abstract projection
estimate.  The distinguished query row is simply assigned speed zero; all
other rows may have arbitrary relative slack speeds.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

set_option maxHeartbeats 1200000

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]
  [DecidableEq ρ] [DecidableEq κ]

/-- The affine denominator of a row under relative motion `d`. -/
def rowDenominator (d : ρ → ℝ) (s : ℝ) (i : ρ) : ℝ := 1 + s * d i

/-- A fixed row frame after each row has been divided by its affine slack
factor. -/
noncomputable def scaledRows (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    Matrix ρ κ ℝ :=
  fun i j => V i j / rowDenominator d s i

/-- Instantaneous logarithmic row-scale speed. -/
noncomputable def scaledRate (d : ρ → ℝ) (s : ℝ) (i : ρ) : ℝ :=
  d i / rowDenominator d s i

/-- Gram matrix of the scaled rows. -/
noncomputable def scaledGram (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    Matrix κ κ ℝ :=
  columnGram (scaledRows V d s)

/-- First derivative of `scaledGram`, written entrywise. -/
noncomputable def scaledGramFirst (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    Matrix κ κ ℝ :=
  fun j k => ∑ i, -2 * d i * V i j * V i k / rowDenominator d s i ^ 3

/-- Second derivative of `scaledGram`, written entrywise. -/
noncomputable def scaledGramSecond (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) :
    Matrix κ κ ℝ :=
  fun j k => ∑ i, 6 * d i ^ 2 * V i j * V i k / rowDenominator d s i ^ 4

theorem hasDerivAt_scaledGram_entry (V : Matrix ρ κ ℝ) (d : ρ → ℝ)
    (s : ℝ) (hden : ∀ i, rowDenominator d s i ≠ 0) (j k : κ) :
    HasDerivAt (fun t => scaledGram V d t j k)
      (scaledGramFirst V d s j k) s := by
  have hterm (i : ρ) :
      HasDerivAt
        (fun t => V i j * V i k / rowDenominator d t i ^ 2)
        (-2 * d i * V i j * V i k / rowDenominator d s i ^ 3) s := by
    have hd : HasDerivAt (fun t : ℝ => rowDenominator d t i) (d i) s := by
      simpa [rowDenominator, add_comm] using
        ((hasDerivAt_id (x := s)).mul_const (d i)).const_add 1
    have hi := (hd.pow 2).inv (pow_ne_zero 2 (hden i))
    have hc := hi.const_mul (V i j * V i k)
    have hc' : HasDerivAt
        (fun t => V i j * V i k / rowDenominator d t i ^ 2)
        (V i j * V i k *
          (-(2 * rowDenominator d s i ^ (2 - 1) * d i) /
            (rowDenominator d s i ^ 2) ^ 2)) s := by
      simpa only [div_eq_mul_inv, Pi.pow_apply, Pi.inv_apply,
        Nat.cast_ofNat] using hc
    have hcoef :
        V i j * V i k *
            (-(2 * rowDenominator d s i ^ (2 - 1) * d i) /
              (rowDenominator d s i ^ 2) ^ 2) =
          -2 * d i * V i j * V i k / rowDenominator d s i ^ 3 := by
      field_simp [hden i]
      ring
    rw [← hcoef]
    exact hc'
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ρ))
    (fun i _ => hterm i)
  have hcurve :
      (∑ i : ρ, fun t => V i j * V i k / rowDenominator d t i ^ 2) =
        (fun t => scaledGram V d t j k) := by
    funext t
    simp only [scaledGram, columnGram, Matrix.mul_apply, Matrix.transpose_apply,
      scaledRows]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, pow_two]
    ring
  rw [hcurve] at hsum
  simpa only [scaledGramFirst] using hsum

theorem hasDerivAt_scaledGramFirst_entry (V : Matrix ρ κ ℝ) (d : ρ → ℝ)
    (s : ℝ) (hden : ∀ i, rowDenominator d s i ≠ 0) (j k : κ) :
    HasDerivAt (fun t => scaledGramFirst V d t j k)
      (scaledGramSecond V d s j k) s := by
  have hterm (i : ρ) :
      HasDerivAt
        (fun t => -2 * d i * V i j * V i k / rowDenominator d t i ^ 3)
        (6 * d i ^ 2 * V i j * V i k / rowDenominator d s i ^ 4) s := by
    have hd : HasDerivAt (fun t : ℝ => rowDenominator d t i) (d i) s := by
      simpa [rowDenominator, add_comm] using
        ((hasDerivAt_id (x := s)).mul_const (d i)).const_add 1
    have hi := (hd.pow 3).inv (pow_ne_zero 3 (hden i))
    have hc := hi.const_mul (-2 * d i * V i j * V i k)
    have hc' : HasDerivAt
        (fun t => -2 * d i * V i j * V i k / rowDenominator d t i ^ 3)
        ((-2 * d i * V i j * V i k) *
          (-(3 * rowDenominator d s i ^ (3 - 1) * d i) /
            (rowDenominator d s i ^ 3) ^ 2)) s := by
      simpa only [div_eq_mul_inv, Pi.pow_apply, Pi.inv_apply,
        Nat.cast_ofNat] using hc
    have hcoef :
        (-2 * d i * V i j * V i k) *
            (-(3 * rowDenominator d s i ^ (3 - 1) * d i) /
              (rowDenominator d s i ^ 3) ^ 2) =
          6 * d i ^ 2 * V i j * V i k / rowDenominator d s i ^ 4 := by
      field_simp [hden i]
      ring
    rw [← hcoef]
    exact hc'
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ρ))
    (fun i _ => hterm i)
  have hcurve :
      (∑ i : ρ, fun t =>
          -2 * d i * V i j * V i k / rowDenominator d t i ^ 3) =
        (fun t => scaledGramFirst V d t j k) := by
    funext t
    simp only [scaledGramFirst, Finset.sum_apply]
  rw [hcurve] at hsum
  simpa only [scaledGramSecond] using hsum

theorem scaledGramFirst_eq (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ)
    (hden : ∀ i, rowDenominator d s i ≠ 0) :
    scaledGramFirst V d s =
      (-2 : ℝ) •
        ((scaledRows V d s).transpose * Matrix.diagonal (scaledRate d s) *
          scaledRows V d s) := by
  ext j k
  simp only [scaledGramFirst, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply, scaledRows, scaledRate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [if_pos]
    field_simp [hden i]
  · intro i' _ hi'
    simp [hi']
  · simp

theorem scaledGramSecond_eq (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ)
    (hden : ∀ i, rowDenominator d s i ≠ 0) :
    scaledGramSecond V d s =
      (6 : ℝ) •
        ((scaledRows V d s).transpose * Matrix.diagonal (scaledRate d s) *
          Matrix.diagonal (scaledRate d s) * scaledRows V d s) := by
  ext j k
  simp only [scaledGramSecond, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply, scaledRows, scaledRate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [if_pos]
    rw [Finset.sum_eq_single i]
    · simp only [if_pos]
      field_simp [hden i]
    · intro i' _ hi'
      simp [hi']
    · simp
  · intro i' _ hi'
    simp [hi']
  · simp

/-- The logarithmic determinant of the augmented scaled Gram matrix. -/
noncomputable def scaledLogDet (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) : ℝ :=
  Real.log (scaledGram V d s).det

/-- Jacobi's first-derivative expression for `scaledLogDet`. -/
noncomputable def scaledLogDetFirst (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) : ℝ :=
  logDetFirstDerivative (scaledGram V d) (scaledGramFirst V d) s

theorem hasDerivAt_scaledLogDet (V : Matrix ρ κ ℝ) (d : ρ → ℝ)
    (s : ℝ) (hden : ∀ i, rowDenominator d s i ≠ 0)
    (hdet : 0 < (scaledGram V d s).det) :
    HasDerivAt (scaledLogDet V d) (scaledLogDetFirst V d s) s := by
  change HasDerivAt (fun t => Real.log (scaledGram V d t).det)
    (((scaledGram V d s)⁻¹ * scaledGramFirst V d s).trace) s
  simpa only using
    hasDerivAt_log_det (fun i j => hasDerivAt_scaledGram_entry V d s hden i j) hdet

theorem hasDerivAt_scaledLogDetFirst (V : Matrix ρ κ ℝ) (d : ρ → ℝ)
    (s : ℝ) (hden : ∀ i, rowDenominator d s i ≠ 0)
    (hunit : IsUnit (scaledGram V d s).det) :
    HasDerivAt (scaledLogDetFirst V d)
      ((-((scaledGram V d s)⁻¹ * scaledGramFirst V d s *
            (scaledGram V d s)⁻¹) * scaledGramFirst V d s +
          (scaledGram V d s)⁻¹ * scaledGramSecond V d s).trace) s := by
  exact hasDerivAt_logDetFirstDerivative
    (fun i j => hasDerivAt_scaledGram_entry V d s hden i j)
    (fun i j => hasDerivAt_scaledGramFirst_entry V d s hden i j)
    rfl hunit

/-- The second-derivative coefficient furnished by Jacobi's formula is the
projection trace curvature. -/
theorem scaledLogDetSecondCoefficient_eq_projection
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ)
    (hden : ∀ i, rowDenominator d s i ≠ 0) :
    (-((scaledGram V d s)⁻¹ * scaledGramFirst V d s *
          (scaledGram V d s)⁻¹) * scaledGramFirst V d s +
        (scaledGram V d s)⁻¹ * scaledGramSecond V d s).trace =
      6 * (rowProjection (scaledRows V d s) *
          Matrix.diagonal (scaledRate d s) *
          Matrix.diagonal (scaledRate d s)).trace -
        4 * (rowProjection (scaledRows V d s) *
          Matrix.diagonal (scaledRate d s) *
          rowProjection (scaledRows V d s) *
          Matrix.diagonal (scaledRate d s)).trace := by
  rw [scaledGramFirst_eq V d s hden, scaledGramSecond_eq V d s hden]
  simpa only [scaledGram, rowProjection] using
    gram_logDetSecond_eq_projection (scaledRows V d s)
      (scaledGram V d s)⁻¹ (scaledRate d s)

/-- Exact block-energy form of the second derivative. -/
noncomputable def scaledProjectionCurvature
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ) : ℝ :=
  let P := rowProjection (scaledRows V d s)
  let D := Matrix.diagonal (scaledRate d s)
  3 * (∑ i, scaledRate d s i ^ 2) - frobeniusSq (P * D * P) -
    3 * frobeniusSq (projectionComplement P * D * projectionComplement P)

theorem hasDerivAt_scaledLogDetFirst_projection
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ)
    (hden : ∀ i, rowDenominator d s i ≠ 0)
    (hunit : IsUnit (scaledGram V d s).det) :
    HasDerivAt (scaledLogDetFirst V d)
      (scaledProjectionCurvature V d s) s := by
  have hderiv := hasDerivAt_scaledLogDetFirst V d s hden hunit
  apply hderiv.congr_deriv
  rw [scaledLogDetSecondCoefficient_eq_projection V d s hden]
  unfold scaledProjectionCurvature
  exact projection_trace_curvature_eq
    (rowProjection_mul_self (scaledRows V d s) (by simpa [scaledGram] using hunit))
    (rowProjection_transpose (scaledRows V d s)) (scaledRate d s)

/-- Strengthened upper bound for the second derivative of the augmented
logarithmic determinant. -/
theorem scaledProjectionCurvature_upper
    (V : Matrix ρ κ ℝ) (d : ρ → ℝ) (s : ℝ)
    (hunit : IsUnit (scaledGram V d s).det) :
    scaledProjectionCurvature V d s ≤
      3 * (∑ i, scaledRate d s i ^ 2) -
        (1 / 2 : ℝ) *
          (Real.sqrt (∑ i, positivePart (scaledRate d s i) ^ 2) -
            Real.sqrt (∑ i, negativePart (scaledRate d s i) ^ 2)) ^ 2 := by
  unfold scaledProjectionCurvature
  exact rowProjection_curvature_upper (scaledRows V d s)
    (by simpa [scaledGram] using hunit) (scaledRate d s)

end StrengthenedCurvature
end SortingAdversary
