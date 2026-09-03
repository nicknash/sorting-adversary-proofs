import SortingAdversary.StrengthenedCurvature.CenterStationarity

/-!
# Coordinate-free whitening identities

The paper states the local geometry using a positive-definite square root.
For Lean, the same facts are shorter when expressed through the electrical
direction `H⁻¹q / √R`: the normalized row motions have total squared energy
one, and the center balance is exactly the leverage-weighted moment identity.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {n : ℕ}

/-- Unit electrical direction for a proposed oriented comparison. -/
noncomputable def electricalDirection (h : History n) (x : Placement n)
    (o : Observation n) : Placement n :=
  (Real.sqrt (effectiveResistance h x o))⁻¹ •
    Matrix.mulVec (barrierHessian h x)⁻¹ (BarrierRow.ofObservation o).normal

/-- The normalized old-row motions induced by a query. -/
noncomputable def electricalMotion (h : History n) (x : Placement n)
    (o : Observation n) (row : BarrierRow n) : ℝ :=
  normalizedRowMotion row x (electricalDirection h x o)

theorem BarrierRow.quadratic_hessianTerm (row : BarrierRow n)
    {x d : Placement n} (hx : row.slack x ≠ 0) :
    d ⬝ᵥ Matrix.mulVec (row.hessianTerm x) d =
      (row.directionalSlack d / row.slack x) ^ 2 := by
  classical
  simp only [dotProduct, Matrix.mulVec, BarrierRow.hessianTerm,
    BarrierRow.directionalSlack]
  calc
    (∑ u, d u * ∑ v, row.normal u * row.normal v / row.slack x ^ 2 * d v) =
        ∑ u, (d u * row.normal u) *
          ((∑ v, d v * row.normal v) / row.slack x ^ 2) := by
      apply Finset.sum_congr rfl
      intro u _
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = (∑ u, d u * row.normal u) *
        ((∑ v, d v * row.normal v) / row.slack x ^ 2) := by
      rw [Finset.sum_mul]
    _ = ((∑ u, row.normal u * d u) / row.slack x) ^ 2 := by
      field_simp [hx]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem barrierHessian_quadratic {h : History n} {x d : Placement n}
    (hx : InHistoryPolytope h x) :
    d ⬝ᵥ Matrix.mulVec (barrierHessian h x) d =
      ((barrierRows h).map fun row => normalizedRowMotion row x d ^ 2).sum := by
  have hslack := barrierRows_slack_pos hx
  unfold barrierHessian
  have aux : ∀ rows : List (BarrierRow n),
      (∀ row ∈ rows, 0 < row.slack x) →
      d ⬝ᵥ Matrix.mulVec
          ((rows.map fun row => row.hessianTerm x).sum) d =
        (rows.map fun row => normalizedRowMotion row x d ^ 2).sum := by
    intro rows hrows
    induction rows with
    | nil => simp [dotProduct]
    | cons row rows ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.add_mulVec,
          dotProduct_add, List.sum_cons]
        rw [row.quadratic_hessianTerm (ne_of_gt (hrows row (by simp)))]
        rw [ih (fun r hr => hrows r (by simp [hr]))]
        rfl
  exact aux (barrierRows h) hslack

private theorem inverse_mulVec_dot_eq {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (q : Placement n) :
    Matrix.mulVec (barrierHessian h x)⁻¹ q ⬝ᵥ q =
      q ⬝ᵥ Matrix.mulVec (barrierHessian h x)⁻¹ q := by
  simpa only [dotProduct, mul_comm]

theorem barrierHessian_mulVec_electricalDirection {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n) :
    Matrix.mulVec (barrierHessian h x) (electricalDirection h x o) =
      (Real.sqrt (effectiveResistance h x o))⁻¹ •
        (BarrierRow.ofObservation o).normal := by
  unfold electricalDirection
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (barrierHessian_posDef hx).det_pos.ne')]
  rw [Matrix.one_mulVec]

theorem electricalDirection_energy_one {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n) :
    electricalDirection h x o ⬝ᵥ
      Matrix.mulVec (barrierHessian h x) (electricalDirection h x o) = 1 := by
  have hR : 0 < effectiveResistance h x o := effectiveResistance_pos hx o
  have hsqrt : 0 < Real.sqrt (effectiveResistance h x o) := Real.sqrt_pos.2 hR
  rw [barrierHessian_mulVec_electricalDirection hx o]
  unfold electricalDirection
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hsquare : Real.sqrt (effectiveResistance h x o) ^ 2 =
      effectiveResistance h x o := Real.sq_sqrt hR.le
  calc
    (∑ i,
      (Real.sqrt (effectiveResistance h x o))⁻¹ *
        Matrix.mulVec (barrierHessian h x)⁻¹
          (BarrierRow.ofObservation o).normal i *
        ((Real.sqrt (effectiveResistance h x o))⁻¹ *
          (BarrierRow.ofObservation o).normal i)) =
        (Real.sqrt (effectiveResistance h x o))⁻¹ ^ 2 *
          (Matrix.mulVec (barrierHessian h x)⁻¹
              (BarrierRow.ofObservation o).normal ⬝ᵥ
            (BarrierRow.ofObservation o).normal) := by
      simp only [dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Real.sqrt (effectiveResistance h x o))⁻¹ ^ 2 *
        effectiveResistance h x o := by
      rw [inverse_mulVec_dot_eq hx]
      rfl
    _ = 1 := by
      field_simp [hsqrt.ne']
      exact hsquare.symm

/-- Equation `∑ᵢ αᵢ² = 1`, without introducing a matrix square root. -/
theorem electricalMotion_energy_one {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n) :
    ((barrierRows h).map fun row => electricalMotion h x o row ^ 2).sum = 1 := by
  unfold electricalMotion
  rw [← barrierHessian_quadratic hx]
  exact electricalDirection_energy_one hx o

theorem electricalMotion_sq_le_one {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n)
    {row : BarrierRow n} (hrow : row ∈ barrierRows h) :
    electricalMotion h x o row ^ 2 ≤ 1 := by
  rw [← electricalMotion_energy_one hx o]
  apply List.single_le_sum
  · intro z hz
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hz
    exact sq_nonneg _
  · exact List.mem_map.mpr ⟨row, hrow, rfl⟩

theorem abs_electricalMotion_le_one {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n)
    {row : BarrierRow n} (hrow : row ∈ barrierRows h) :
    |electricalMotion h x o row| ≤ 1 := by
  have hsq := electricalMotion_sq_le_one hx o hrow
  nlinarith [sq_nonneg (|electricalMotion h x o row|),
    sq_abs (electricalMotion h x o row)]

/-- Equation `∑ᵢ σᵢ αᵢ = 0`. -/
theorem IsVolumetricCenter.electrical_balance {h : History n}
    {x : Placement n} (hc : IsVolumetricCenter h x) (o : Observation n) :
    ((barrierRows h).map fun row =>
      rowLeverage h x row * electricalMotion h x o row).sum = 0 := by
  exact hc.leverage_balance (electricalDirection h x o)

end StrengthenedCurvature
end SortingAdversary
