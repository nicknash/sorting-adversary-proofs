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

theorem scaledRankOne_posSemidef (q : ι → ℝ) (s : ℝ) :
    (scaledRankOne q s).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [scaledRankOne, Matrix.conjTranspose_apply, mul_comm]
  · intro z
    by_cases hs : s = 0
    · simp [scaledRankOne, hs, dotProduct, Matrix.mulVec]
    · rw [show star z = z by ext i; simp]
      simp only [dotProduct, Matrix.mulVec, scaledRankOne]
      rw [show (∑ i, z i * ∑ j, q i * q j / s ^ 2 * z j) =
          (∑ i, z i * q i) ^ 2 / s ^ 2 by
        calc
          (∑ i, z i * ∑ j, q i * q j / s ^ 2 * z j) =
              ∑ i, (z i * q i) * ((∑ j, z j * q j) / s ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ i, z i * q i) * ((∑ j, z j * q j) / s ^ 2) := by
            rw [Finset.sum_mul]
          _ = (∑ i, z i * q i) ^ 2 / s ^ 2 := by ring]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)

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

private theorem nonsingInv_unique_entry (M : Matrix Unit Unit ℝ) :
    M⁻¹ default default = (M default default)⁻¹ := by
  rw [Matrix.inv_def]
  simp [Matrix.det_unique, Matrix.adjugate_apply, Ring.inverse_eq_inv]

/-- Sherman--Morrison for the normalized rank-one update used by a new
comparison row.  It is proved from mathlib's Woodbury identity, with the
one-dimensional middle matrix expanded explicitly. -/
theorem nonsingInv_add_scaledRankOne (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (q : ι → ℝ) (s : ℝ) (hs : s ≠ 0) :
    (A + scaledRankOne q s)⁻¹ = fun i j => A⁻¹ i j -
      Matrix.mulVec A⁻¹ q i * Matrix.mulVec A⁻¹ q j /
        (s ^ 2 + q ⬝ᵥ Matrix.mulVec A⁻¹ q) := by
  classical
  let U : Matrix ι Unit ℝ := Matrix.replicateCol Unit (fun i => q i / s)
  let V : Matrix Unit ι ℝ := Matrix.replicateRow Unit (fun j => q j / s)
  let C : Matrix Unit Unit ℝ := 1
  have hAunit : IsUnit A := hA.isUnit
  have hCunit : IsUnit C := by simp [C]
  have hR : 0 ≤ q ⬝ᵥ Matrix.mulVec A⁻¹ q :=
    hA.posSemidef.inv.dotProduct_mulVec_nonneg q
  have hinvEntry (u v : ι) : A⁻¹ u v = A⁻¹ v u := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M v u)
      hA.posSemidef.inv.isHermitian.eq
    simpa [Matrix.conjTranspose_apply] using h
  have hquad :
      (V * A⁻¹ * U) default default =
        (q ⬝ᵥ Matrix.mulVec A⁻¹ q) / s ^ 2 := by
    simp only [Matrix.mul_apply, U, V, Matrix.replicateCol,
      Matrix.replicateRow, Finset.univ_unique, Finset.sum_singleton,
      Matrix.mulVec, dotProduct]
    change (∑ x, (∑ y, q y / s * A⁻¹ y x) * (q x / s)) =
      (∑ x, q x * ∑ y, A⁻¹ x y * q y) / s ^ 2
    field_simp [hs]
    simp_rw [hinvEntry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hs]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hs]
  have hmiddleEntry :
      (C⁻¹ + V * A⁻¹ * U) default default =
        1 + (q ⬝ᵥ Matrix.mulVec A⁻¹ q) / s ^ 2 := by
    simp only [C, inv_one, Matrix.one_apply, if_pos, Matrix.add_apply]
    rw [hquad]
  have hmiddlePos : 0 < 1 +
      (q ⬝ᵥ Matrix.mulVec A⁻¹ q) / s ^ 2 := by
    have hsquare : 0 < s ^ 2 := sq_pos_of_ne_zero hs
    positivity
  have hmiddleUnit : IsUnit (C⁻¹ + V * A⁻¹ * U) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_unique]
    rw [hmiddleEntry]
    exact isUnit_iff_ne_zero.mpr hmiddlePos.ne'
  have hupdate : U * C * V = scaledRankOne q s := by
    ext i j
    simp [U, V, C, Matrix.mul_apply, scaledRankOne]
    field_simp [hs]
  rw [← hupdate,
    Matrix.add_mul_mul_inv_eq_sub A U C V hAunit hCunit hmiddleUnit]
  ext i j
  simp only [Matrix.sub_apply, Pi.sub_apply]
  congr 1
  have hleft (u : ι) : (A⁻¹ * U) u default =
      Matrix.mulVec A⁻¹ q u / s := by
    simp only [Matrix.mul_apply, U, Matrix.replicateCol, Matrix.mulVec,
      dotProduct, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    simp [U, Matrix.replicateCol]
    ring
  have hright (v : ι) : (V * A⁻¹) default v =
      Matrix.mulVec A⁻¹ q v / s := by
    simp only [Matrix.mul_apply, V, Matrix.replicateRow, Matrix.mulVec]
    change (∑ u, (q u / s) * A⁻¹ u v) =
      (∑ u, A⁻¹ v u * q u) / s
    simp_rw [hinvEntry]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hfactor :
      A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ =
        (A⁻¹ * U) * (C⁻¹ + V * A⁻¹ * U)⁻¹ * (V * A⁻¹) := by
    simp only [Matrix.mul_assoc]
  rw [hfactor]
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton,
    hleft, hright]
  rw [show (C⁻¹ + V * A⁻¹ * U)⁻¹ default default =
      (1 + (q ⬝ᵥ Matrix.mulVec A⁻¹ q) / s ^ 2)⁻¹ by
    rw [nonsingInv_unique_entry, hmiddleEntry]]
  have hden : s ^ 2 + q ⬝ᵥ Matrix.mulVec A⁻¹ q ≠ 0 := by
    have hsquare : 0 < s ^ 2 := sq_pos_of_ne_zero hs
    positivity
  field_simp [hs, hden]

/-- Quadratic-form version of Sherman--Morrison. -/
theorem quadratic_nonsingInv_add_scaledRankOne
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q r : ι → ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    r ⬝ᵥ Matrix.mulVec (A + scaledRankOne q s)⁻¹ r =
      r ⬝ᵥ Matrix.mulVec A⁻¹ r -
        (r ⬝ᵥ Matrix.mulVec A⁻¹ q) ^ 2 /
          (s ^ 2 + q ⬝ᵥ Matrix.mulVec A⁻¹ q) := by
  rw [nonsingInv_add_scaledRankOne A hA q s hs]
  let u : ι → ℝ := Matrix.mulVec A⁻¹ q
  let D : ℝ := s ^ 2 + q ⬝ᵥ Matrix.mulVec A⁻¹ q
  change (∑ i, r i * ∑ j,
      (A⁻¹ i j - u i * u j / D) * r j) =
    (∑ i, r i * ∑ j, A⁻¹ i j * r j) -
      (∑ i, r i * u i) ^ 2 / D
  have hsymm : (∑ j, u j * r j) = ∑ i, r i * u i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    (∑ i, r i * ∑ j, (A⁻¹ i j - u i * u j / D) * r j) =
        (∑ i, r i * ∑ j, A⁻¹ i j * r j) -
          (∑ i, r i * u i) * (∑ j, u j * r j) / D := by
            simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub]
            rw [Finset.sum_sub_distrib]
            congr 1
            simp_rw [div_eq_mul_inv]
            calc
              (∑ i, r i * ∑ j, u i * u j * D⁻¹ * r j) =
                  ∑ i, (r i * u i) * (∑ j, u j * r j) * D⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [show (r i * u i * ∑ j, u j * r j) * D⁻¹ =
                        (r i * u i * D⁻¹) * ∑ j, u j * r j by ring]
                    conv_lhs => rw [Finset.mul_sum]
                    conv_rhs => rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
              _ = (∑ i, r i * u i) * (∑ j, u j * r j) * D⁻¹ := by
                    rw [Finset.sum_mul, Finset.sum_mul]
              _ = _ := by ring
    _ = _ := by rw [hsymm]; ring

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
