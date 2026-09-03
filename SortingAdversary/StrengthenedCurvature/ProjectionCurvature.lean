import SortingAdversary.StrengthenedCurvature.SignImbalance
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Projection form of the strengthened curvature saving

This file supplies the finite-dimensional algebra behind equations (25)--(32)
of the strengthened-curvature source.  The calculus of the augmented Hessian
is separated from the projection estimate: here a symmetric idempotent matrix
is treated abstractly, and the sign-imbalance loss is proved entrywise.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complementary projection. -/
def projectionComplement (P : Matrix ι ι ℝ) : Matrix ι ι ℝ := 1 - P

/-- The self-adjoint involution associated with a projection. -/
def projectionReflection (P : Matrix ι ι ℝ) : Matrix ι ι ℝ := (2 : ℝ) • P - 1

/-- Squared Frobenius norm, kept as an exact finite sum. -/
def frobeniusSq (A : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Frobenius inner product, written entrywise. -/
def frobeniusInner (A B : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The block-diagonal energy of a diagonal operator relative to `P`. -/
def blockDiagonalEnergy (P : Matrix ι ι ℝ) (d : ι → ℝ) : ℝ :=
  frobeniusSq (P * Matrix.diagonal d * P) +
    frobeniusSq
      (projectionComplement P * Matrix.diagonal d * projectionComplement P)

/-- The reflection-average expression equal to the block-diagonal energy. -/
noncomputable def reflectionAverageEnergy (P : Matrix ι ι ℝ) (d : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((∑ i, d i ^ 2) +
      ∑ i, ∑ j, d i * d j * projectionReflection P i j ^ 2)

theorem projectionComplement_mul_self {P : Matrix ι ι ℝ}
    (hP : P * P = P) :
    projectionComplement P * projectionComplement P = projectionComplement P := by
  unfold projectionComplement
  noncomm_ring [hP]

theorem projection_mul_complement {P : Matrix ι ι ℝ}
    (hP : P * P = P) :
    P * projectionComplement P = 0 := by
  unfold projectionComplement
  noncomm_ring [hP]

theorem complement_mul_projection {P : Matrix ι ι ℝ}
    (hP : P * P = P) :
    projectionComplement P * P = 0 := by
  unfold projectionComplement
  noncomm_ring [hP]

theorem projectionReflection_mul_self {P : Matrix ι ι ℝ}
    (hP : P * P = P) :
    projectionReflection P * projectionReflection P = 1 := by
  unfold projectionReflection
  rw [two_smul]
  noncomm_ring [hP]

theorem projectionReflection_transpose {P : Matrix ι ι ℝ}
    (hPsymm : P.transpose = P) :
    (projectionReflection P).transpose = projectionReflection P := by
  ext i j
  have hentry := congrArg (fun A : Matrix ι ι ℝ => A j i) hPsymm
  simp only [Matrix.transpose_apply] at hentry
  by_cases hij : i = j
  · subst j
    rfl
  · simp [projectionReflection, Matrix.one_apply, hij, Ne.symm hij, hentry]

theorem frobeniusInner_eq_trace (A B : Matrix ι ι ℝ) :
    frobeniusInner A B = (A.transpose * B).trace := by
  simp only [frobeniusInner, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem frobeniusSq_eq_trace (A : Matrix ι ι ℝ) :
    frobeniusSq A = (A.transpose * A).trace := by
  rw [← frobeniusInner_eq_trace]
  unfold frobeniusSq frobeniusInner
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frobeniusSq_add (A B : Matrix ι ι ℝ) :
    frobeniusSq (A + B) =
      frobeniusSq A + frobeniusSq B + 2 * frobeniusInner A B := by
  unfold frobeniusSq frobeniusInner
  simp only [Matrix.add_apply]
  simp_rw [add_sq]
  simp only [Finset.sum_add_distrib]
  have hcross :
      (∑ i, ∑ j, 2 * A i j * B i j) =
        2 * ∑ i, ∑ j, A i j * B i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcross]
  ring

theorem frobeniusSq_smul (c : ℝ) (A : Matrix ι ι ℝ) :
    frobeniusSq (c • A) = c ^ 2 * frobeniusSq A := by
  unfold frobeniusSq
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem frobeniusInner_smul_left (c : ℝ) (A B : Matrix ι ι ℝ) :
    frobeniusInner (c • A) B = c * frobeniusInner A B := by
  unfold frobeniusInner
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frobeniusInner_eq_zero_of_mul_eq_zero
    {A B : Matrix ι ι ℝ} (hA : A.transpose = A) (hAB : A * B = 0) :
    frobeniusInner A B = 0 := by
  rw [frobeniusInner_eq_trace, hA, hAB, Matrix.trace_zero]

@[simp] theorem frobeniusSq_diagonal (d : ι → ℝ) :
    frobeniusSq (Matrix.diagonal d) = ∑ i, d i ^ 2 := by
  classical
  unfold frobeniusSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

theorem diagonal_reflection_inner {P : Matrix ι ι ℝ}
    (hPsymm : P.transpose = P) (d : ι → ℝ) :
    frobeniusInner (Matrix.diagonal d)
        (projectionReflection P * Matrix.diagonal d * projectionReflection P) =
      ∑ i, ∑ j, d i * d j * projectionReflection P i j ^ 2 := by
  classical
  have hJsymm := projectionReflection_transpose hPsymm
  have hdiag : (Matrix.diagonal d).transpose = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  rw [frobeniusInner_eq_trace]
  rw [hdiag]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single j]
    · simp only [if_pos, mul_one]
      have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) hJsymm
      simp only [Matrix.transpose_apply] at hentry
      rw [hentry]
      ring
    · intro k _ hkj
      simp [hkj]
    · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem frobeniusSq_reflection_conjugate {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (d : ι → ℝ) :
    frobeniusSq
        (projectionReflection P * Matrix.diagonal d * projectionReflection P) =
      frobeniusSq (Matrix.diagonal d) := by
  let J := projectionReflection P
  let D := Matrix.diagonal d
  have hJ : J * J = 1 := projectionReflection_mul_self hP
  have hJT : J.transpose = J := projectionReflection_transpose hPsymm
  have hDT : D.transpose = D := by simp [D]
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace]
  have hconjT : (J * D * J).transpose = J * D * J := by
    simp only [Matrix.transpose_mul, hJT, hDT]
    rw [Matrix.mul_assoc]
  rw [show projectionReflection P * Matrix.diagonal d * projectionReflection P =
      J * D * J by rfl]
  rw [hconjT, hDT]
  calc
    ((J * D * J) * (J * D * J)).trace =
        (J * (D * J * J * D) * J).trace := by
      congr 1
      noncomm_ring
    _ = ((D * J * J * D) * J * J).trace := by
      exact (Matrix.trace_mul_cycle (D * J * J * D) J J).symm
    _ = (D * D).trace := by
      congr 1
      noncomm_ring [hJ]

/-- Twice the block-diagonal operator is its reflection symmetrization. -/
theorem two_smul_blockDiagonal {P : Matrix ι ι ℝ} (d : ι → ℝ) :
    (2 : ℝ) •
        (P * Matrix.diagonal d * P +
          projectionComplement P * Matrix.diagonal d * projectionComplement P) =
      Matrix.diagonal d +
        projectionReflection P * Matrix.diagonal d * projectionReflection P := by
  unfold projectionComplement projectionReflection
  rw [two_smul]
  simp only [two_smul]
  noncomm_ring

theorem blockDiagonal_eq_reflectionAverage {P : Matrix ι ι ℝ} (d : ι → ℝ) :
    P * Matrix.diagonal d * P +
        projectionComplement P * Matrix.diagonal d * projectionComplement P =
      (1 / 2 : ℝ) •
        (Matrix.diagonal d +
          projectionReflection P * Matrix.diagonal d * projectionReflection P) := by
  have htwice := two_smul_blockDiagonal (P := P) d
  ext i j
  have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) htwice
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hentry ⊢
  linarith

theorem blockDiagonalEnergy_eq_reflectionAverage {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (d : ι → ℝ) :
    blockDiagonalEnergy P d = reflectionAverageEnergy P d := by
  let D := Matrix.diagonal d
  let Q := projectionComplement P
  let J := projectionReflection P
  let A := P * D * P
  let B := Q * D * Q
  have hDT : D.transpose = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, Matrix.diagonal, hij, Ne.symm hij]
  have hQT : Q.transpose = Q := by
    unfold Q projectionComplement
    ext i j
    have hentry := congrArg (fun M : Matrix ι ι ℝ => M j i) hPsymm
    simp only [Matrix.transpose_apply] at hentry
    by_cases hij : i = j
    · subst j
      rfl
    · simp [Matrix.one_apply, hij, Ne.symm hij, hentry]
  have hAT : A.transpose = A := by
    unfold A
    simp only [Matrix.transpose_mul, hPsymm, hDT]
    rw [Matrix.mul_assoc]
  have hBT : B.transpose = B := by
    unfold B
    simp only [Matrix.transpose_mul, hQT, hDT]
    rw [Matrix.mul_assoc]
  have hPQ : P * Q = 0 := by
    simpa [Q] using projection_mul_complement hP
  have hAB : A * B = 0 := by
    unfold A B
    calc
      (P * D * P) * (Q * D * Q) = P * D * (P * Q) * D * Q := by
        noncomm_ring
      _ = 0 := by rw [hPQ]; simp
  have hinner : frobeniusInner A B = 0 :=
    frobeniusInner_eq_zero_of_mul_eq_zero hAT hAB
  have hsum : frobeniusSq A + frobeniusSq B = frobeniusSq (A + B) := by
    rw [frobeniusSq_add, hinner]
    ring
  have havg : A + B = (1 / 2 : ℝ) • (D + J * D * J) := by
    simpa [A, B, D, Q, J] using blockDiagonal_eq_reflectionAverage (P := P) d
  have hconj : frobeniusSq (J * D * J) = frobeniusSq D := by
    simpa [J, D] using frobeniusSq_reflection_conjugate hP hPsymm d
  have hcross : frobeniusInner D (J * D * J) =
      ∑ i, ∑ j, d i * d j * J i j ^ 2 := by
    simpa [J, D] using diagonal_reflection_inner hPsymm d
  unfold blockDiagonalEnergy reflectionAverageEnergy
  change frobeniusSq A + frobeniusSq B = _
  rw [hsum, havg, frobeniusSq_smul, frobeniusSq_add, hconj, hcross]
  simp only [D, frobeniusSq_diagonal]
  ring

theorem frobeniusSq_nonneg (A : Matrix ι ι ℝ) : 0 ≤ frobeniusSq A := by
  unfold frobeniusSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem reflection_row_sq_sum {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (i : ι) :
    ∑ j, projectionReflection P i j ^ 2 = 1 := by
  have hJ := projectionReflection_mul_self hP
  have hii := congrArg (fun A : Matrix ι ι ℝ => A i i) hJ
  simp only [Matrix.mul_apply, Matrix.one_apply, if_pos] at hii
  have hsymm := projectionReflection_transpose hPsymm
  have hentry (j : ι) :
      projectionReflection P j i = projectionReflection P i j := by
    have := congrArg (fun A : Matrix ι ι ℝ => A i j) hsymm
    simpa using this
  simpa [hentry, pow_two] using hii

theorem reflection_col_sq_sum {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (j : ι) :
    ∑ i, projectionReflection P i j ^ 2 = 1 := by
  have hsymm := projectionReflection_transpose hPsymm
  calc
    ∑ i, projectionReflection P i j ^ 2 =
        ∑ i, projectionReflection P j i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have := congrArg (fun A : Matrix ι ι ℝ => A j i) hsymm
      simp only [Matrix.transpose_apply] at this
      rw [this]
    _ = 1 := reflection_row_sq_sum hP hPsymm j

/-- The squared entries of a reflection form a doubly stochastic matrix. -/
theorem reflectionSquares_doublyStochastic {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) :
    (∀ i j, 0 ≤ projectionReflection P i j ^ 2) ∧
      (∀ i, ∑ j, projectionReflection P i j ^ 2 ≤ 1) ∧
      (∀ j, ∑ i, projectionReflection P i j ^ 2 ≤ 1) := by
  refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
  · intro i
    rw [reflection_row_sq_sum hP hPsymm i]
  · intro j
    rw [reflection_col_sq_sum hP hPsymm j]

private theorem partSquares (x : ℝ) :
    x ^ 2 = positivePart x ^ 2 + negativePart x ^ 2 := by
  rcases le_total x 0 with hx | hx
  · simp [positivePart, negativePart, hx]
  · simp [positivePart, negativePart, hx]

theorem sum_sq_eq_partSquares (d : ι → ℝ) :
    (∑ i, d i ^ 2) =
      (∑ i, positivePart (d i) ^ 2) +
        ∑ i, negativePart (d i) ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact partSquares (d i)

/-- Sign imbalance forces energy into the block-diagonal part.  This is the
numerical heart of the strengthened curvature estimate. -/
theorem reflectionAverageEnergy_lower {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (d : ι → ℝ) :
    (1 / 2 : ℝ) *
        (Real.sqrt (∑ i, positivePart (d i) ^ 2) -
          Real.sqrt (∑ i, negativePart (d i) ^ 2)) ^ 2 ≤
      reflectionAverageEnergy P d := by
  let pos := ∑ i, positivePart (d i) ^ 2
  let neg := ∑ i, negativePart (d i) ^ 2
  have hstoch := reflectionSquares_doublyStochastic hP hPsymm
  have hcross := doublySubstochastic_quadratic_lower d
    (fun i j => projectionReflection P i j ^ 2)
    hstoch.1 hstoch.2.1 hstoch.2.2
  have hpos : 0 ≤ pos :=
    Finset.sum_nonneg fun i _ => sq_nonneg (positivePart (d i))
  have hneg : 0 ≤ neg :=
    Finset.sum_nonneg fun i _ => sq_nonneg (negativePart (d i))
  have hsqrtPos : Real.sqrt pos ^ 2 = pos := Real.sq_sqrt hpos
  have hsqrtNeg : Real.sqrt neg ^ 2 = neg := Real.sq_sqrt hneg
  have hsum : (∑ i, d i ^ 2) = pos + neg := by
    simpa [pos, neg] using sum_sq_eq_partSquares d
  unfold reflectionAverageEnergy
  rw [hsum]
  simp only [pos, neg] at hcross hsqrtPos hsqrtNeg ⊢
  nlinarith [Real.sqrt_nonneg pos, Real.sqrt_nonneg neg]

/-- Abstract strengthened curvature inequality for a symmetric projection. -/
theorem projection_curvature_upper {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (d : ι → ℝ) :
    3 * (∑ i, d i ^ 2) -
        frobeniusSq (P * Matrix.diagonal d * P) -
        3 * frobeniusSq
          (projectionComplement P * Matrix.diagonal d * projectionComplement P) ≤
      3 * (∑ i, d i ^ 2) -
        (1 / 2 : ℝ) *
          (Real.sqrt (∑ i, positivePart (d i) ^ 2) -
            Real.sqrt (∑ i, negativePart (d i) ^ 2)) ^ 2 := by
  have himbalance := reflectionAverageEnergy_lower hP hPsymm d
  rw [← blockDiagonalEnergy_eq_reflectionAverage hP hPsymm d] at himbalance
  have hW : 0 ≤ frobeniusSq
      (projectionComplement P * Matrix.diagonal d * projectionComplement P) :=
    frobeniusSq_nonneg _
  unfold blockDiagonalEnergy at himbalance
  nlinarith

/-- The trace form produced by differentiating `log det` is exactly the
block-energy form used by `projection_curvature_upper`. -/
theorem projection_trace_curvature_eq {P : Matrix ι ι ℝ}
    (hP : P * P = P) (hPsymm : P.transpose = P) (d : ι → ℝ) :
    6 * (P * Matrix.diagonal d * Matrix.diagonal d).trace -
        4 * (P * Matrix.diagonal d * P * Matrix.diagonal d).trace =
      3 * (∑ i, d i ^ 2) -
        frobeniusSq (P * Matrix.diagonal d * P) -
        3 * frobeniusSq
          (projectionComplement P * Matrix.diagonal d * projectionComplement P) := by
  let D := Matrix.diagonal d
  let Q := projectionComplement P
  have hDT : D.transpose = D := by simp [D]
  have hQT : Q.transpose = Q := by
    unfold Q projectionComplement
    simp [hPsymm]
  have hQ : Q * Q = Q := by
    simpa [Q] using projectionComplement_mul_self hP
  have hTP : frobeniusSq (P * D * P) = (P * D * P * D).trace := by
    rw [frobeniusSq_eq_trace]
    have htrans : (P * D * P).transpose = P * D * P := by
      simp only [Matrix.transpose_mul, hPsymm, hDT]
      rw [Matrix.mul_assoc]
    rw [htrans]
    calc
      ((P * D * P) * (P * D * P)).trace =
          ((P * D * P * D) * P).trace := by
        apply congrArg Matrix.trace
        calc
          (P * D * P) * (P * D * P) =
              P * D * (P * P) * D * P := by simp only [Matrix.mul_assoc]
          _ = (P * D * P * D) * P := by rw [hP]
      _ = (P * (P * D * P * D)).trace := Matrix.trace_mul_comm _ _
      _ = (P * D * P * D).trace := by
        apply congrArg Matrix.trace
        calc
          P * (P * D * P * D) = (P * P) * D * P * D := by
            simp only [Matrix.mul_assoc]
          _ = P * D * P * D := by rw [hP]
  have hTQ : frobeniusSq (Q * D * Q) = (Q * D * Q * D).trace := by
    rw [frobeniusSq_eq_trace]
    have htrans : (Q * D * Q).transpose = Q * D * Q := by
      simp only [Matrix.transpose_mul, hQT, hDT]
      rw [Matrix.mul_assoc]
    rw [htrans]
    calc
      ((Q * D * Q) * (Q * D * Q)).trace =
          ((Q * D * Q * D) * Q).trace := by
        apply congrArg Matrix.trace
        calc
          (Q * D * Q) * (Q * D * Q) =
              Q * D * (Q * Q) * D * Q := by simp only [Matrix.mul_assoc]
          _ = (Q * D * Q * D) * Q := by rw [hQ]
      _ = (Q * (Q * D * Q * D)).trace := Matrix.trace_mul_comm _ _
      _ = (Q * D * Q * D).trace := by
        apply congrArg Matrix.trace
        calc
          Q * (Q * D * Q * D) = (Q * Q) * D * Q * D := by
            simp only [Matrix.mul_assoc]
          _ = Q * D * Q * D := by rw [hQ]
  have hdiagTrace : (D * D).trace = ∑ i, d i ^ 2 := by
    simp [D, Matrix.trace, pow_two]
  have hcycle : (D * P * D).trace = (P * D * D).trace := by
    simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle P D D).symm
  have hW : (Q * D * Q * D).trace =
      (D * D).trace - 2 * (P * D * D).trace +
        (P * D * P * D).trace := by
    unfold Q projectionComplement
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.trace_sub]
    rw [hcycle]
    ring
  rw [show Matrix.diagonal d = D by rfl, hTP, hTQ, hW, hdiagTrace]
  ring

section RowProjection

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]
  [DecidableEq ρ] [DecidableEq κ]

/-- Gram matrix of the columns of an augmented row matrix. -/
def columnGram (V : Matrix ρ κ ℝ) : Matrix κ κ ℝ := V.transpose * V

/-- Orthogonal projection onto the column space of a full-column-rank matrix. -/
noncomputable def rowProjection (V : Matrix ρ κ ℝ) : Matrix ρ ρ ℝ :=
  V * (columnGram V)⁻¹ * V.transpose

/-- Jacobi's second-derivative trace expression for a row Gram matrix, in
row-projection coordinates. -/
theorem gram_logDetSecond_eq_projection (A : Matrix ρ κ ℝ)
    (R : Matrix κ κ ℝ) (d : ρ → ℝ) :
    (-((R * ((-2 : ℝ) •
          (A.transpose * Matrix.diagonal d * A)) * R)) *
          ((-2 : ℝ) • (A.transpose * Matrix.diagonal d * A)) +
        R * ((6 : ℝ) •
          (A.transpose * Matrix.diagonal d * Matrix.diagonal d * A))).trace =
      6 * ((A * R * A.transpose) * Matrix.diagonal d *
          Matrix.diagonal d).trace -
        4 * ((A * R * A.transpose) * Matrix.diagonal d *
          (A * R * A.transpose) * Matrix.diagonal d).trace := by
  let D := Matrix.diagonal d
  let X := A.transpose * D * A
  let Y := A.transpose * D * D * A
  let P := A * R * A.transpose
  have hmatrix :
      -(R * ((-2 : ℝ) • X) * R) * ((-2 : ℝ) • X) +
          R * ((6 : ℝ) • Y) =
        (-4 : ℝ) • (R * X * R * X) + (6 : ℝ) • (R * Y) := by
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, neg_mul,
      neg_neg, smul_smul]
    module
  have hcycleX : (R * X * R * X).trace = (P * D * P * D).trace := by
    calc
      (R * X * R * X).trace =
          ((R * A.transpose * D * A * R * A.transpose * D) * A).trace := by
        apply congrArg Matrix.trace
        simp only [X, Matrix.mul_assoc]
      _ = (A * (R * A.transpose * D * A * R * A.transpose * D)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (P * D * P * D).trace := by
        apply congrArg Matrix.trace
        simp only [P, Matrix.mul_assoc]
  have hcycleY : (R * Y).trace = (P * D * D).trace := by
    calc
      (R * Y).trace = ((R * A.transpose * D * D) * A).trace := by
        apply congrArg Matrix.trace
        simp only [Y, Matrix.mul_assoc]
      _ = (A * (R * A.transpose * D * D)).trace := Matrix.trace_mul_comm _ _
      _ = (P * D * D).trace := by
        apply congrArg Matrix.trace
        simp only [P, Matrix.mul_assoc]
  change
    (-((R * ((-2 : ℝ) • X) * R)) * ((-2 : ℝ) • X) +
        R * ((6 : ℝ) • Y)).trace = _
  rw [hmatrix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    hcycleX, hcycleY]
  change _ = 6 * (P * D * D).trace - 4 * (P * D * P * D).trace
  ring

theorem columnGram_transpose (V : Matrix ρ κ ℝ) :
    (columnGram V).transpose = columnGram V := by
  unfold columnGram
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem rowProjection_transpose (V : Matrix ρ κ ℝ) :
    (rowProjection V).transpose = rowProjection V := by
  unfold rowProjection
  have hG := columnGram_transpose V
  simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hG,
    Matrix.transpose_transpose]
  rw [Matrix.mul_assoc]

theorem rowProjection_mul_self (V : Matrix ρ κ ℝ)
    (hunit : IsUnit (columnGram V).det) :
    rowProjection V * rowProjection V = rowProjection V := by
  unfold rowProjection
  calc
    (V * (columnGram V)⁻¹ * V.transpose) *
          (V * (columnGram V)⁻¹ * V.transpose) =
        V * (columnGram V)⁻¹ * (V.transpose * V) *
          (columnGram V)⁻¹ * V.transpose := by
      simp only [Matrix.mul_assoc]
    _ = V * (columnGram V)⁻¹ * columnGram V *
          (columnGram V)⁻¹ * V.transpose := by rfl
    _ = V * (columnGram V)⁻¹ * V.transpose := by
      calc
        V * (columnGram V)⁻¹ * columnGram V *
              (columnGram V)⁻¹ * V.transpose =
            V * (((columnGram V)⁻¹ * columnGram V) *
              ((columnGram V)⁻¹ * V.transpose)) := by
          simp only [Matrix.mul_assoc]
        _ = V * ((1 : Matrix κ κ ℝ) *
              ((columnGram V)⁻¹ * V.transpose)) := by
          have hInv : (columnGram V)⁻¹ * columnGram V =
              (1 : Matrix κ κ ℝ) := Matrix.nonsing_inv_mul _ hunit
          congr 1
          rw [hInv]
        _ = V * (columnGram V)⁻¹ * V.transpose := by
          simp [Matrix.mul_assoc]

/-- The strengthened projection estimate specialized to an augmented row
matrix. -/
theorem rowProjection_curvature_upper (V : Matrix ρ κ ℝ)
    (hunit : IsUnit (columnGram V).det) (d : ρ → ℝ) :
    3 * (∑ i, d i ^ 2) -
        frobeniusSq (rowProjection V * Matrix.diagonal d * rowProjection V) -
        3 * frobeniusSq
          (projectionComplement (rowProjection V) * Matrix.diagonal d *
            projectionComplement (rowProjection V)) ≤
      3 * (∑ i, d i ^ 2) -
        (1 / 2 : ℝ) *
          (Real.sqrt (∑ i, positivePart (d i) ^ 2) -
            Real.sqrt (∑ i, negativePart (d i) ^ 2)) ^ 2 :=
  projection_curvature_upper (rowProjection_mul_self V hunit)
    (rowProjection_transpose V) d

end RowProjection

end StrengthenedCurvature
end SortingAdversary
