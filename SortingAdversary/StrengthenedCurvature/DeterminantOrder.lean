import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing

/-!
# Determinant monotonicity for positive matrices

Mathlib supplies the spectral theorem and positive-(semi)definite matrix
calculus, but not the finite-dimensional determinant monotonicity lemma in the
form needed by the volumetric potential.  This file proves that lemma from the
square-root factorization and the spectral theorem.
 -/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adding a positive-semidefinite real matrix to the identity cannot decrease
the determinant. -/
theorem one_le_det_one_add_of_posSemidef
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    1 ≤ (1 + C).det := by
  classical
  let U := hC.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal hC.isHermitian.eigenvalues
  have hCeq : C = (U : Matrix ι ι ℝ) * D *
      star (U : Matrix ι ι ℝ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hC.isHermitian.spectral_theorem
  have hU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 :=
    U.property.2
  have hconj :
      1 + C = (U : Matrix ι ι ℝ) * (1 + D) *
        star (U : Matrix ι ι ℝ) := by
    rw [hCeq]
    calc
      1 + (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) =
          (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) +
            (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) := by rw [hU]
      _ = (U : Matrix ι ι ℝ) * (1 + D) *
          star (U : Matrix ι ι ℝ) := by
        noncomm_ring
  have hdetU :
      (U : Matrix ι ι ℝ).det *
        (star (U : Matrix ι ι ℝ)).det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  have hdiag : (1 + D).det = ∏ i, (1 + hC.isHermitian.eigenvalues i) := by
    rw [show 1 + D = Matrix.diagonal
        (fun i => 1 + hC.isHermitian.eigenvalues i) by
      ext i j
      by_cases hij : i = j <;> simp [D, Matrix.diagonal, hij]]
    exact Matrix.det_diagonal
  rw [hconj, Matrix.det_mul, Matrix.det_mul, hdiag]
  calc
    (U : Matrix ι ι ℝ).det * (∏ i, (1 + hC.isHermitian.eigenvalues i)) *
          (star (U : Matrix ι ι ℝ)).det =
        (∏ i, (1 + hC.isHermitian.eigenvalues i)) *
          ((U : Matrix ι ι ℝ).det *
            (star (U : Matrix ι ι ℝ)).det) := by ring
    _ = ∏ i, (1 + hC.isHermitian.eigenvalues i) := by rw [hdetU, mul_one]
    _ ≥ 1 := Finset.one_le_prod fun i _ => by
      linarith [hC.eigenvalues_nonneg i]

/-- Loewner monotonicity of determinant on positive-definite real matrices. -/
theorem det_le_det_add_of_posDef_of_posSemidef
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosSemidef) :
    A.det ≤ (A + B).det := by
  classical
  let S : Matrix ι ι ℝ := CFC.sqrt A
  have hAnonneg : (0 : Matrix ι ι ℝ) ≤ A := hA.posSemidef.nonneg
  have hSnonneg : S.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hSsq : S ^ 2 = A := CFC.sq_sqrt A hAnonneg
  have hSdet : S.det ≠ 0 := by
    rw [hA.posSemidef.det_sqrt]
    simpa using ne_of_gt (Real.sqrt_pos.2 hA.det_pos)
  have hSunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr
    (isUnit_iff_ne_zero.mpr hSdet)
  let C : Matrix ι ι ℝ := (S⁻¹).conjTranspose * B * S⁻¹
  have hSinvHermitian : (S⁻¹).conjTranspose = S⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    exact congrArg Inv.inv hSnonneg.isHermitian.eq
  have hC : C.PosSemidef := by
    dsimp only [C]
    exact hB.conjTranspose_mul_mul_same S⁻¹
  have hfactor : A + B = S.conjTranspose * (1 + C) * S := by
    have hSinvS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S
      ((Matrix.isUnit_iff_isUnit_det S).mp hSunit)
    have hSSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
      ((Matrix.isUnit_iff_isUnit_det S).mp hSunit)
    have hSHermitian : S.conjTranspose = S := hSnonneg.isHermitian.eq
    rw [hSHermitian]
    dsimp only [C]
    calc
      A + B = S * S + B := by simpa [pow_two] using congrArg (fun M => M + B) hSsq.symm
      _ = S * (1 + ((S⁻¹).conjTranspose * B * S⁻¹)) * S := by
        rw [hSinvHermitian]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
          Matrix.mul_assoc, hSinvS, hSSinv]
        rw [← Matrix.mul_assoc S S⁻¹ B, hSSinv, Matrix.one_mul]
  have hdetfactor :
      (A + B).det = A.det * (1 + C).det := by
    rw [hfactor, Matrix.det_mul, Matrix.det_mul]
    have hAdet : A.det = S.conjTranspose.det * S.det := by
      rw [hSnonneg.isHermitian.eq, ← Matrix.det_mul, ← pow_two, hSsq]
    rw [hAdet]
    ring
  rw [hdetfactor]
  exact le_mul_of_one_le_right hA.det_pos.le
    (one_le_det_one_add_of_posSemidef hC)

end StrengthenedCurvature
end SortingAdversary
