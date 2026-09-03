import SortingAdversary.StrengthenedCurvature.Barrier
import SortingAdversary.StrengthenedCurvature.DeterminantOrder
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp

/-!
# Rank-one barrier updates

This packages the matrix-determinant lemma in the exact entrywise form used
when a comparison row is appended at a fixed feasible placement.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def scaledRankOne (q : ι → ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  fun i j => q i * q j / s ^ 2

theorem det_add_rankOne (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (q : ι → ℝ) (s : ℝ) (hs : s ≠ 0) :
    (A + scaledRankOne q s).det =
      A.det * (1 + (q ⬝ᵥ Matrix.mulVec A⁻¹ q) / s ^ 2) := by
  classical
  let U : Matrix ι Unit ℝ := Matrix.replicateCol Unit q
  let V : Matrix Unit ι ℝ := Matrix.replicateRow Unit (fun j => q j / s ^ 2)
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hUV : U * V = scaledRankOne q s := by
    ext i j
    simp [U, V, Matrix.mul_apply, scaledRankOne]
    ring
  rw [← hUV, Matrix.det_add_mul U V hAunit]
  congr 1
  rw [Matrix.det_unique]
  change 1 + (V * A⁻¹ * U) default default =
    1 + (q ⬝ᵥ Matrix.mulVec A⁻¹ q) / s ^ 2
  congr 1
  simp [Matrix.mul_apply, U, V, Matrix.replicateRow, Matrix.replicateCol,
    Matrix.mulVec, dotProduct]
  field_simp
  have hinv_symm (i j : ι) : A⁻¹ i j = A⁻¹ j i := by
    have hentry := congrArg (fun M : Matrix ι ι ℝ => M j i)
      (hA.posSemidef.inv.isHermitian.eq)
    simpa [Matrix.conjTranspose_apply] using hentry
  calc
    s ^ 2 * ∑ i, (∑ j, q j * A⁻¹ j i / s ^ 2) * q i =
        ∑ i, ∑ j, q i * A⁻¹ i j * q j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hinv_symm j i]
      field_simp
    _ = ∑ i, q i * ∑ j, A⁻¹ i j * q j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem barrierHessian_cons (o : Observation n) (h : History n)
    (x : Placement n) :
    barrierHessian (o :: h) x =
      barrierHessian h x + (BarrierRow.ofObservation o).hessianTerm x := by
  simp [barrierHessian, barrierRows, List.sum_append, add_comm, add_assoc]

/-- Exact determinant ratio after adjoining one comparison row at the same
placement. -/
theorem det_barrierHessian_cons {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (hslack : (BarrierRow.ofObservation o).slack x ≠ 0) :
    (barrierHessian (o :: h) x).det =
      (barrierHessian h x).det *
        (1 + ((BarrierRow.ofObservation o).normal ⬝ᵥ
          Matrix.mulVec (barrierHessian h x)⁻¹ (BarrierRow.ofObservation o).normal) /
            (BarrierRow.ofObservation o).slack x ^ 2) := by
  rw [barrierHessian_cons]
  exact det_add_rankOne _ (barrierHessian_posDef hx) _ _ hslack

/-- Effective resistance of an oriented comparison normal in the current
barrier metric. -/
noncomputable def effectiveResistance (h : History n) (x : Placement n)
    (o : Observation n) : ℝ :=
  (BarrierRow.ofObservation o).normal ⬝ᵥ
    Matrix.mulVec (barrierHessian h x)⁻¹ (BarrierRow.ofObservation o).normal

theorem effectiveResistance_pos {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) :
    0 < effectiveResistance h x o := by
  have hq := (BarrierRow.ofObservation_normal_ne_zero o)
  have hpos := (barrierHessian_posDef hx).inv.dotProduct_mulVec_pos hq
  simpa [effectiveResistance] using hpos

/-- Algebraic large-offset estimate: if the normalized rank-one update is at
most `K-1`, adjoining the row multiplies the determinant by at most `K`. -/
theorem det_barrierHessian_cons_le {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (hslack : 0 < (BarrierRow.ofObservation o).slack x)
    {K : ℝ}
    (hquot : effectiveResistance h x o /
      (BarrierRow.ofObservation o).slack x ^ 2 ≤ K - 1) :
    (barrierHessian (o :: h) x).det ≤ K * (barrierHessian h x).det := by
  rw [det_barrierHessian_cons hx o hslack.ne']
  have hdet : 0 < (barrierHessian h x).det := (barrierHessian_posDef hx).det_pos
  change (barrierHessian h x).det *
      (1 + effectiveResistance h x o /
        (BarrierRow.ofObservation o).slack x ^ 2) ≤ _
  nlinarith

theorem volumetricValue₂_cons_sub_le {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (hslack : 0 < (BarrierRow.ofObservation o).slack x)
    {K : ℝ} (hK : 1 ≤ K)
    (hquot : effectiveResistance h x o /
      (BarrierRow.ofObservation o).slack x ^ 2 ≤ K - 1) :
    volumetricValue₂ (o :: h) x - volumetricValue₂ h x ≤
      Real.log K / (2 * Real.log 2) := by
  have hxchild : InHistoryPolytope (o :: h) x := by
    refine ⟨hx.1, ?_⟩
    simpa using And.intro
      ((BarrierRow.realizesPlacement_iff_slack_pos o x).2 hslack) hx.2
  have hdet := det_barrierHessian_cons_le hx o hslack hquot
  have holdpos : 0 < (barrierHessian h x).det := (barrierHessian_posDef hx).det_pos
  have hnewpos : 0 < (barrierHessian (o :: h) x).det :=
    (barrierHessian_posDef hxchild).det_pos
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hlogdet : Real.log (barrierHessian (o :: h) x).det ≤
      Real.log K + Real.log (barrierHessian h x).det := by
    calc
      Real.log (barrierHessian (o :: h) x).det ≤
          Real.log (K * (barrierHessian h x).det) :=
        Real.strictMonoOn_log.monotoneOn hnewpos (mul_pos hKpos holdpos) hdet
      _ = _ := Real.log_mul hKpos.ne' holdpos.ne'
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [volumetricValue₂, volumetricValue, volumetricValue₂, volumetricValue]
  rw [show
    1 / 2 * Real.log (barrierHessian (o :: h) x).det / Real.log 2 -
        1 / 2 * Real.log (barrierHessian h x).det / Real.log 2 =
      (1 / 2 * Real.log (barrierHessian (o :: h) x).det -
        1 / 2 * Real.log (barrierHessian h x).det) / Real.log 2 by ring]
  rw [show Real.log K / (2 * Real.log 2) =
      (1 / 2 * Real.log K) / Real.log 2 by ring]
  apply (div_le_div_iff_of_pos_right hlogtwo).2
  nlinarith

end StrengthenedCurvature
end SortingAdversary
