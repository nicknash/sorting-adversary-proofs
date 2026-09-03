import SortingAdversary.StrengthenedCurvature.DeterminantOrder
import SortingAdversary.StrengthenedCurvature.HistoryPolytope
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Order

/-!
# The grounded path determinant

The lower boundary row followed by the `n - 1` adjacent-comparison rows has a
unit lower-triangular incidence matrix.  Consequently its weighted Gram
matrix has determinant equal to the product of its edge weights.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

/-- Incidence matrix of a path grounded at its lower endpoint.  Row zero is
the lower-boundary edge; row `i > 0` is the edge from `i-1` to `i`. -/
def pathIncidence (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if j = i then 1 else if j.val + 1 = i.val then -1 else 0

@[simp] theorem pathIncidence_diagonal (i : Fin n) :
    pathIncidence n i i = 1 := by
  simp [pathIncidence]

theorem pathIncidence_isLowerTriangular :
    (pathIncidence n).IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  have hne : j ≠ i := by
    intro h
    subst j
    simp at hij
  have hnot : j.val + 1 ≠ i.val := by omega
  simp [pathIncidence, hne, hnot]

@[simp] theorem pathIncidence_det : (pathIncidence n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ pathIncidence_isLowerTriangular]
  simp

/-- Weighted Hessian of the grounded path. -/
noncomputable def pathHessian (s : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (pathIncidence n).conjTranspose * Matrix.diagonal (fun i => 1 / s i ^ 2) *
    pathIncidence n

theorem pathHessian_det (s : Fin n → ℝ) :
    (pathHessian s).det = ∏ i, 1 / s i ^ 2 := by
  classical
  simp [pathHessian, Matrix.det_mul, Matrix.det_diagonal]

theorem pathHessian_posDef (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) :
    (pathHessian s).PosDef := by
  have hdiag : (Matrix.diagonal (fun i => 1 / s i ^ 2) :
      Matrix (Fin n) (Fin n) ℝ).PosDef :=
    Matrix.PosDef.diagonal fun i => div_pos zero_lt_one (sq_pos_of_pos (hs i))
  unfold pathHessian
  apply hdiag.conjTranspose_mul_mul_same
  apply Matrix.mulVec_injective_of_det_ne_zero
  simp

/-- Put the canonical path back on the labelled item coordinates. -/
noncomputable def labelledPathHessian (π : Ranking n) (s : Fin n → ℝ) :
    Matrix (Item n) (Item n) ℝ :=
  Matrix.reindex π.symm π.symm (pathHessian s)

theorem labelledPathHessian_det (π : Ranking n) (s : Fin n → ℝ) :
    (labelledPathHessian π s).det = ∏ i, 1 / s i ^ 2 := by
  rw [labelledPathHessian, Matrix.det_reindex_self, pathHessian_det]

theorem labelledPathHessian_posDef (π : Ranking n) (s : Fin n → ℝ)
    (hs : ∀ i, 0 < s i) : (labelledPathHessian π s).PosDef := by
  exact (pathHessian_posDef s hs).submatrix π.injective

/-- The `i`th grounded-path slack in labelled coordinates. -/
def labelledPathSlack (π : Ranking n) (x : Placement n) (i : Fin n) : ℝ :=
  if hi : i.val = 0 then x (π.symm i)
  else x (π.symm i) - x (π.symm ⟨i.val - 1,
    (Nat.sub_lt (Nat.zero_lt_of_ne_zero hi) (by omega)).trans i.isLt⟩)

theorem pathIncidence_apply_rank_zero (π : Ranking n) (i : Fin n)
    (hi : i.val = 0) (u : Item n) :
    pathIncidence n i (π u) = if u = π.symm i then 1 else 0 := by
  by_cases hu : u = π.symm i
  · subst u
    simp [pathIncidence]
  · have hne : π u ≠ i := by
      intro h
      apply hu
      simpa using congrArg π.symm h
    have hsucc : (π u).val + 1 ≠ i.val := by omega
    simp [pathIncidence, hne, hsucc, hu]

theorem pathIncidence_apply_rank_positive (π : Ranking n) (i : Fin n)
    (hi : i.val ≠ 0) (u : Item n) :
    pathIncidence n i (π u) =
      if u = π.symm i then 1
      else if u = π.symm ⟨i.val - 1,
        (Nat.sub_lt (Nat.zero_lt_of_ne_zero hi) (by omega)).trans i.isLt⟩
      then -1 else 0 := by
  let p : Fin n := ⟨i.val - 1,
    (Nat.sub_lt (Nat.zero_lt_of_ne_zero hi) (by omega)).trans i.isLt⟩
  by_cases hu : u = π.symm i
  · subst u
    simp [pathIncidence]
  · have hupper : π u ≠ i := by
      intro h
      apply hu
      simpa using congrArg π.symm h
    by_cases hp : u = π.symm p
    · subst u
      have hpi : p ≠ i := by
        intro h
        have := congrArg Fin.val h
        dsimp [p] at this
        omega
      have hpred : (π (π.symm p)).val + 1 = i.val := by
        simp [p]
        omega
      simp [pathIncidence, hpi, hu, p]
      omega
    · have hpred : (π u).val + 1 ≠ i.val := by
        intro h
        have heq : π u = p := by
          apply Fin.ext
          dsimp [p]
          omega
        apply hp
        simpa using congrArg π.symm heq
      simp [pathIncidence, hupper, hpred, hu, hp, p]

/-- The rank-one contribution of one grounded-path row. -/
noncomputable def labelledPathTerm (π : Ranking n) (x : Placement n) (i : Fin n) :
    Matrix (Item n) (Item n) ℝ := fun u v =>
  pathIncidence n i (π u) * pathIncidence n i (π v) /
    labelledPathSlack π x i ^ 2

theorem labelledPathHessian_apply (π : Ranking n) (x : Placement n)
    (u v : Item n) :
    labelledPathHessian π (labelledPathSlack π x) u v =
      ∑ i : Fin n, labelledPathTerm π x i u v := by
  classical
  rw [labelledPathHessian]
  change pathHessian (labelledPathSlack π x) (π u) (π v) = _
  simp only [labelledPathTerm]
  unfold pathHessian
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [Matrix.diagonal]
    ring
  · intro j _ hji
    simp [Matrix.diagonal, hji]
  · simp

end StrengthenedCurvature
end SortingAdversary
