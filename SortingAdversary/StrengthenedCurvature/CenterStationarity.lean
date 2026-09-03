import SortingAdversary.StrengthenedCurvature.CenterExistence
import SortingAdversary.StrengthenedCurvature.MatrixCalculus
import Mathlib.Tactic.FunProp

/-!
# First-order balance at a volumetric center

This file differentiates the retained-row Hessian along an arbitrary affine
line.  Since the history polytope is open, a genuine volumetric center is an
unconstrained local minimum, and Jacobi's formula gives the exact directional
stationarity equation used by the whitening argument.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {n : ℕ}

/-- Motion of a row slack in direction `d`. -/
noncomputable def BarrierRow.directionalSlack (row : BarrierRow n)
    (d : Placement n) : ℝ :=
  ∑ v, row.normal v * d v

/-- Entrywise derivative of a row Hessian along a direction. -/
noncomputable def BarrierRow.hessianDirectionalDerivative
    (row : BarrierRow n) (x d : Placement n) :
    Matrix (Item n) (Item n) ℝ :=
  fun u v => -2 * row.normal u * row.normal v * row.directionalSlack d /
    row.slack x ^ 3

/-- Derivative of the full retained-row Hessian along a direction. -/
noncomputable def barrierHessianDirectionalDerivative
    (h : History n) (x d : Placement n) :
    Matrix (Item n) (Item n) ℝ :=
  ((barrierRows h).map fun row => row.hessianDirectionalDerivative x d).sum

/-- Leverage score of a retained row in the old Hessian. -/
noncomputable def rowLeverage (h : History n) (x : Placement n)
    (row : BarrierRow n) : ℝ :=
  (row.normal ⬝ᵥ Matrix.mulVec (barrierHessian h x)⁻¹ row.normal) /
    row.slack x ^ 2

/-- A row's relative slack motion. -/
noncomputable def normalizedRowMotion (row : BarrierRow n) (x d : Placement n) : ℝ :=
  row.directionalSlack d / row.slack x

theorem BarrierRow.slack_line (row : BarrierRow n) (x d : Placement n)
    (t : ℝ) :
    row.slack (x + t • d) = row.slack x + t * row.directionalSlack d := by
  classical
  unfold slack directionalSlack
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ v, row.normal v * (x v + t * d v)) - row.boundary =
        ((∑ v, row.normal v * x v) +
          ∑ v, t * (row.normal v * d v)) - row.boundary := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = (∑ v, row.normal v * x v) - row.boundary +
        ∑ v, t * (row.normal v * d v) := by ring
    _ = (∑ v, row.normal v * x v) - row.boundary +
        t * ∑ v, row.normal v * d v := by rw [Finset.mul_sum]

theorem BarrierRow.hasDerivAt_slack_line (row : BarrierRow n)
    (x d : Placement n) :
    HasDerivAt (fun t : ℝ => row.slack (x + t • d))
      (row.directionalSlack d) 0 := by
  rw [show (fun t : ℝ => row.slack (x + t • d)) =
      (fun t => row.slack x + t * row.directionalSlack d) by
    funext t
    exact row.slack_line x d t]
  simpa [add_comm] using
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const (row.directionalSlack d)).const_add
      (row.slack x)

theorem BarrierRow.hasDerivAt_hessianTerm_line_entry
    (row : BarrierRow n) {x d : Placement n}
    (hx : 0 < row.slack x) (u v : Item n) :
    HasDerivAt (fun t : ℝ => row.hessianTerm (x + t • d) u v)
      (row.hessianDirectionalDerivative x d u v) 0 := by
  have hs := row.hasDerivAt_slack_line x d
  have hs0 : row.slack (x + (0 : ℝ) • d) ≠ 0 := by
    simpa using hx.ne'
  have hi := (hs.pow 2).inv (pow_ne_zero 2 hs0)
  have hc := hi.const_mul (row.normal u * row.normal v)
  have hfun :
      (fun t : ℝ => row.normal u * row.normal v *
        ((fun z : ℝ => row.slack (x + z • d)) ^ 2)⁻¹ t) =
      (fun t : ℝ => row.hessianTerm (x + t • d) u v) := by
    funext t
    simp only [BarrierRow.hessianTerm, Pi.pow_apply, Pi.inv_apply]
    rw [div_eq_mul_inv]
  rw [hfun] at hc
  have hcoef :
      row.normal u * row.normal v *
        (-(↑2 * row.slack (x + (0 : ℝ) • d) ^ (2 - 1) *
          row.directionalSlack d) /
          ((fun t : ℝ => row.slack (x + t • d)) ^ 2) 0 ^ 2) =
      row.hessianDirectionalDerivative x d u v := by
    simp only [Pi.zero_apply, zero_smul, add_zero, Pi.pow_apply,
      Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
    unfold BarrierRow.hessianDirectionalDerivative
    field_simp [hx.ne']
  rw [← hcoef]
  exact hc

theorem hasDerivAt_barrierHessian_line_entry {h : History n}
    {x d : Placement n} (hx : InHistoryPolytope h x) (u v : Item n) :
    HasDerivAt (fun t : ℝ => barrierHessian h (x + t • d) u v)
      (barrierHessianDirectionalDerivative h x d u v) 0 := by
  have hslack := barrierRows_slack_pos hx
  unfold barrierHessian barrierHessianDirectionalDerivative
  have aux : ∀ rows : List (BarrierRow n),
      (∀ row ∈ rows, 0 < row.slack x) →
      HasDerivAt
        (fun t : ℝ =>
          (rows.map fun row => row.hessianTerm (x + t • d)).sum u v)
        ((rows.map fun row => row.hessianDirectionalDerivative x d).sum u v) 0 := by
    intro rows hrows
    induction rows with
    | nil =>
        simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
    | cons row rows ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.add_apply]
        exact (row.hasDerivAt_hessianTerm_line_entry
          (hrows row (by simp)) u v).add
          (ih fun r hr => hrows r (by simp [hr]))
  exact aux (barrierRows h) hslack

private theorem trace_mul_hessianDirectionalDerivative
    (A : Matrix (Item n) (Item n) ℝ) (row : BarrierRow n)
    {x d : Placement n} (hx : row.slack x ≠ 0) :
    (A * row.hessianDirectionalDerivative x d).trace =
      -2 * ((row.normal ⬝ᵥ Matrix.mulVec A row.normal) / row.slack x ^ 2) *
        (row.directionalSlack d / row.slack x) := by
  classical
  simp only [Matrix.trace, Matrix.mul_apply,
    BarrierRow.hessianDirectionalDerivative, dotProduct, Matrix.mulVec]
  calc
    (∑ i, ∑ j, A i j *
        (-2 * row.normal j * row.normal i * row.directionalSlack d /
          row.slack x ^ 3)) =
        ∑ i, (-2 * row.directionalSlack d / row.slack x ^ 3 * row.normal i) *
          ∑ j, A i j * row.normal j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (-2 * row.directionalSlack d / row.slack x ^ 3) *
        ∑ i, row.normal i * ∑ j, A i j * row.normal j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = -2 * ((∑ i, row.normal i * ∑ j, A i j * row.normal j) /
          row.slack x ^ 2) *
        (row.directionalSlack d / row.slack x) := by
      field_simp [hx]

theorem trace_barrierHessianDirectionalDerivative {h : History n}
    {x d : Placement n} (hx : InHistoryPolytope h x) :
    ((barrierHessian h x)⁻¹ *
      barrierHessianDirectionalDerivative h x d).trace =
      -2 * (((barrierRows h).map fun row =>
        rowLeverage h x row * normalizedRowMotion row x d).sum) := by
  have hslack := barrierRows_slack_pos hx
  unfold barrierHessianDirectionalDerivative
  have aux : ∀ rows : List (BarrierRow n),
      (∀ row ∈ rows, 0 < row.slack x) →
      ((barrierHessian h x)⁻¹ *
        (rows.map fun row => row.hessianDirectionalDerivative x d).sum).trace =
        -2 * ((rows.map fun row =>
          rowLeverage h x row * normalizedRowMotion row x d).sum) := by
    intro rows hrows
    induction rows with
    | nil => simp
    | cons row rows ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.trace_add]
        rw [trace_mul_hessianDirectionalDerivative _ row
          (ne_of_gt (hrows row (by simp)))]
        rw [ih (fun r hr => hrows r (by simp [hr]))]
        unfold rowLeverage normalizedRowMotion
        ring
  exact aux (barrierRows h) hslack

/-- The strict history polytope is open in placement space. -/
theorem isOpen_historyPolytope (h : History n) :
    IsOpen {x : Placement n | InHistoryPolytope h x} := by
  have hopenRows : ∀ rows : List (BarrierRow n),
      IsOpen {x : Placement n | ∀ row ∈ rows, 0 < row.slack x} := by
    intro rows
    induction rows with
    | nil => simp
    | cons row rows ih =>
        rw [show {x : Placement n | ∀ r ∈ row :: rows, 0 < r.slack x} =
            {x | 0 < row.slack x} ∩
              {x | ∀ r ∈ rows, 0 < r.slack x} by
          ext x
          simp]
        exact (isOpen_lt continuous_const
          (continuous_barrierRow_slack row)).inter ih
  have hiff (x : Placement n) :
      InHistoryPolytope h x ↔ ∀ row ∈ barrierRows h, 0 < row.slack x := by
    constructor
    · exact barrierRows_slack_pos
    · intro hs
      constructor
      · intro v
        constructor
        · simpa using hs (BarrierRow.lowerBox v) (by
            simp [barrierRows, boxRows])
        · have hu := hs (BarrierRow.upperBox v) (by
            simp [barrierRows, boxRows])
          simpa [sub_pos] using hu
      · rw [List.forall_iff_forall_mem]
        intro o ho
        apply (BarrierRow.realizesPlacement_iff_slack_pos o x).2
        apply hs (BarrierRow.ofObservation o)
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨o, ho, rfl⟩
  rw [show {x : Placement n | InHistoryPolytope h x} =
      {x : Placement n | ∀ row ∈ barrierRows h, 0 < row.slack x} by
    ext x
    exact hiff x]
  exact hopenRows (barrierRows h)

theorem hasDerivAt_volumetricValue_line {h : History n}
    {x d : Placement n} (hx : InHistoryPolytope h x) :
    HasDerivAt (fun t : ℝ => volumetricValue h (x + t • d))
      ((1 / 2 : ℝ) *
        ((barrierHessian h x)⁻¹ *
          barrierHessianDirectionalDerivative h x d).trace) 0 := by
  have hlog := hasDerivAt_log_det
    (M := fun t : ℝ => barrierHessian h (x + t • d))
    (M' := barrierHessianDirectionalDerivative h x d) (s := 0)
    (fun u v => hasDerivAt_barrierHessian_line_entry hx u v)
    (by simpa using (barrierHessian_posDef hx).det_pos)
  have hv := hlog.const_mul (1 / 2 : ℝ)
  simpa [volumetricValue] using hv

/-- Every directional derivative of the volumetric value vanishes at a
genuine center. -/
theorem IsVolumetricCenter.trace_stationarity {h : History n}
    {x : Placement n} (hc : IsVolumetricCenter h x) (d : Placement n) :
    ((barrierHessian h x)⁻¹ *
      barrierHessianDirectionalDerivative h x d).trace = 0 := by
  let path : ℝ → Placement n := fun t => x + t • d
  have hpathContinuous : Continuous path := by
    fun_prop
  have hnhds : {t : ℝ | InHistoryPolytope h (path t)} ∈ nhds 0 := by
    have hopen := (isOpen_historyPolytope h).preimage hpathContinuous
    apply hopen.mem_nhds
    simpa [path] using hc.1
  have hminOn : IsMinOn (fun t : ℝ => volumetricValue h (path t))
      {t : ℝ | InHistoryPolytope h (path t)} 0 := by
    intro _ ht
    simpa [path] using hc.2 _ ht
  have hlocal := hminOn.isLocalMin hnhds
  have hderiv := hasDerivAt_volumetricValue_line (d := d) hc.1
  have hderivPath : HasDerivAt
      (fun t : ℝ => volumetricValue h (path t))
      ((1 / 2 : ℝ) *
        ((barrierHessian h x)⁻¹ *
          barrierHessianDirectionalDerivative h x d).trace) 0 := by
    simpa [path] using hderiv
  have hzero := hlocal.hasDerivAt_eq_zero hderivPath
  nlinarith

/-- The center equation in leverage-score form, equation (5) of the source. -/
theorem IsVolumetricCenter.leverage_balance {h : History n}
    {x : Placement n} (hc : IsVolumetricCenter h x) (d : Placement n) :
    ((barrierRows h).map fun row =>
      rowLeverage h x row * normalizedRowMotion row x d).sum = 0 := by
  have htrace := hc.trace_stationarity d
  rw [trace_barrierHessianDirectionalDerivative hc.1] at htrace
  linarith

end StrengthenedCurvature
end SortingAdversary
