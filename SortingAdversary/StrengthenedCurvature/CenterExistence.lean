import SortingAdversary.StrengthenedCurvature.VolumetricCenter
import SortingAdversary.StrengthenedCurvature.RankOneDeterminant
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
import Mathlib.Algebra.Group.Pi.Units

/-!
# Existence of the volumetric center

Sublevel sets stay a positive distance from every barrier hyperplane.  They
are therefore closed subsets of the compact unit cube, so the volumetric
value attains its infimum.  This supplies the minimizer used by the local
curvature argument without adding a center-existence axiom.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {n : ℕ}

private theorem ringInverse_pi_apply {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, f i ≠ 0) (i : ι) : Ring.inverse f i = (f i)⁻¹ := by
  have hunit : IsUnit f := Pi.isUnit_iff.mpr fun j => isUnit_iff_ne_zero.mpr (hf j)
  obtain ⟨u, rfl⟩ := hunit
  simp [Ring.inverse_unit]

theorem lowerBoxHessian_det (x : Placement n) :
    (lowerBoxHessian x).det = ∏ v, 1 / x v ^ 2 := by
  rw [lowerBoxHessian_eq_diagonal, Matrix.det_diagonal]

theorem upperBoxHessian_det (x : Placement n) :
    (upperBoxHessian x).det = ∏ v, 1 / (1 - x v) ^ 2 := by
  rw [upperBoxHessian_eq_diagonal, Matrix.det_diagonal]

private theorem lower_factor_one_le {x : Placement n} (hx : InUnitBox x)
    (v : Item n) : 1 ≤ 1 / x v ^ 2 := by
  apply one_le_one_div
  · exact sq_pos_of_pos (hx v).1
  · nlinarith [(hx v).1, (hx v).2]

private theorem upper_factor_one_le {x : Placement n} (hx : InUnitBox x)
    (v : Item n) : 1 ≤ 1 / (1 - x v) ^ 2 := by
  apply one_le_one_div
  · exact sq_pos_of_pos (sub_pos.2 (hx v).2)
  · nlinarith [(hx v).1, (hx v).2]

theorem lower_coordinate_det_le {x : Placement n} (hx : InUnitBox x)
    (v : Item n) :
    1 / x v ^ 2 ≤ (barrierHessian h x).det := by
  rw [barrierHessian_eq_lower_add]
  have hproduct : 1 / x v ^ 2 ≤ ∏ u, 1 / x u ^ 2 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => 1 / x u ^ 2)
      (Finset.mem_univ v)]
    exact le_mul_of_one_le_right (by positivity)
      (Finset.one_le_prod fun u _ => lower_factor_one_le hx u)
  refine hproduct.trans ?_
  rw [← lowerBoxHessian_det]
  exact det_le_det_add_of_posDef_of_posSemidef
    (lowerBoxHessian_posDef hx) (hessianTerms_posSemidef _ x)

theorem upper_coordinate_det_le {x : Placement n} (hx : InUnitBox x)
    (v : Item n) :
    1 / (1 - x v) ^ 2 ≤ (barrierHessian h x).det := by
  rw [barrierHessian_eq_upper_add]
  have hproduct : 1 / (1 - x v) ^ 2 ≤ ∏ u, 1 / (1 - x u) ^ 2 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => 1 / (1 - x u) ^ 2)
      (Finset.mem_univ v)]
    exact le_mul_of_one_le_right (by positivity)
      (Finset.one_le_prod fun u _ => upper_factor_one_le hx u)
  refine hproduct.trans ?_
  rw [← upperBoxHessian_det]
  exact det_le_det_add_of_posDef_of_posSemidef
    (upperBoxHessian_posDef hx) (hessianTerms_posSemidef _ x)

private theorem exists_sum_remainder {α : Type*} [AddCommMonoid α]
    (a : α) : ∀ {xs : List α}, a ∈ xs →
      ∃ rest : List α, xs.sum = a + rest.sum ∧ rest ⊆ xs
  | [], h => by simp at h
  | b :: xs, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · exact ⟨xs, by simp, fun _ hm => by simp [hm]⟩
      · obtain ⟨rest, hrest, hsub⟩ := exists_sum_remainder a htail
        exact ⟨b :: rest,
          by simp [hrest, add_comm, add_left_comm, add_assoc],
          fun _ hm => by
            rcases List.mem_cons.mp hm with rfl | hm
            · simp
            · simp [hsub hm]⟩

private theorem sum_posSemidef (rows : List (Matrix (Item n) (Item n) ℝ))
    (hrows : ∀ M ∈ rows, M.PosSemidef) : rows.sum.PosSemidef := by
  induction rows with
  | nil => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Item n) (Item n) ℝ).PosSemidef)
  | cons M rows ih =>
      simp only [List.sum_cons]
      exact (hrows M (by simp)).add (ih fun N hN => hrows N (by simp [hN]))

private theorem barrierHessian_eq_lower_row_add_remainder
    {h : History n} {x : Placement n} {o : Observation n} (ho : o ∈ h) :
    ∃ remainder : List (Matrix (Item n) (Item n) ℝ),
      barrierHessian h x =
        (lowerBoxHessian x + (BarrierRow.ofObservation o).hessianTerm x) +
          remainder.sum ∧
      remainder.sum.PosSemidef := by
  let rows : List (BarrierRow n) :=
    (List.ofFn fun v : Item n => BarrierRow.upperBox v) ++
      h.map BarrierRow.ofObservation
  have hterm : (BarrierRow.ofObservation o).hessianTerm x ∈
      (rows.map fun row => row.hessianTerm x) := by
    apply List.mem_map.mpr
    refine ⟨BarrierRow.ofObservation o, ?_, rfl⟩
    dsimp only [rows]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨o, ho, rfl⟩
  obtain ⟨remainder, hsum, hsubset⟩ :=
    exists_sum_remainder ((BarrierRow.ofObservation o).hessianTerm x) hterm
  refine ⟨remainder, ?_, ?_⟩
  · rw [barrierHessian_eq_lower_add]
    change lowerBoxHessian x +
      (rows.map fun row => row.hessianTerm x).sum = _
    rw [hsum]
    simp [add_assoc]
  · apply sum_posSemidef remainder
    intro M hM
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp (hsubset hM)
    exact row.hessianTerm_posSemidef x

theorem lowerBoxHessian_inv_apply {x : Placement n} (hx : InUnitBox x)
    (u v : Item n) :
    (lowerBoxHessian x)⁻¹ u v = if u = v then x u ^ 2 else 0 := by
  rw [lowerBoxHessian_eq_diagonal, Matrix.inv_diagonal]
  by_cases huv : u = v
  · subst v
    rw [Matrix.diagonal_apply_eq]
    simp only [if_pos]
    rw [ringInverse_pi_apply]
    · simp [one_div]
    · intro i
      exact div_ne_zero one_ne_zero (pow_ne_zero 2 (ne_of_gt (hx i).1))
  · simp [Matrix.diagonal, huv]

theorem lowerBox_effectiveResistance (x : Placement n) (hx : InUnitBox x)
    (o : Observation n) :
    (BarrierRow.ofObservation o).normal ⬝ᵥ
        Matrix.mulVec (lowerBoxHessian x)⁻¹
          (BarrierRow.ofObservation o).normal =
      x (upper o) ^ 2 + x (lower o) ^ 2 := by
  classical
  have hmul : Matrix.mulVec (lowerBoxHessian x)⁻¹
      (BarrierRow.ofObservation o).normal =
      fun v => x v ^ 2 * (BarrierRow.ofObservation o).normal v := by
    funext u
    simp only [Matrix.mulVec, dotProduct, lowerBoxHessian_inv_apply hx]
    rw [Finset.sum_eq_single u]
    · simp
    · intro b _ hbu
      simp [Ne.symm hbu]
    · simp
  rw [hmul]
  simp only [dotProduct, BarrierRow.ofObservation_normal_eq]
  rw [show
    (∑ v,
      (if v = upper o then 1 else if v = lower o then -1 else 0) *
        (x v ^ 2 *
          (if v = upper o then 1 else if v = lower o then -1 else 0))) =
      ∑ v, ((if v = upper o then x (upper o) ^ 2 else 0) +
        (if v = lower o then x (lower o) ^ 2 else 0)) by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hvu : v = upper o
    · subst v
      simp [Ne.symm (BarrierRow.lower_ne_upper o)]
    · by_cases hvl : v = lower o
      · subst v
        simp [hvu]
      · simp [hvu, hvl]]
  simp [Finset.sum_add_distrib]

theorem comparison_slack_det_le {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) {o : Observation n} (ho : o ∈ h) :
    1 / (BarrierRow.ofObservation o).slack x ^ 2 ≤
      (barrierHessian h x).det := by
  let q := (BarrierRow.ofObservation o).normal
  let s := (BarrierRow.ofObservation o).slack x
  have hs : 0 < s := by
    exact (BarrierRow.realizesPlacement_iff_slack_pos o x).1
      ((List.forall_iff_forall_mem.1 hx.2) o ho)
  have hD : (lowerBoxHessian x).PosDef := lowerBoxHessian_posDef hx.1
  have hterm : (BarrierRow.ofObservation o).hessianTerm x =
      scaledRankOne q s := rfl
  have hformula :
      (lowerBoxHessian x + (BarrierRow.ofObservation o).hessianTerm x).det =
        (lowerBoxHessian x).det *
          (1 + (q ⬝ᵥ Matrix.mulVec (lowerBoxHessian x)⁻¹ q) / s ^ 2) := by
    rw [hterm]
    exact det_add_rankOne _ hD q s hs.ne'
  have hres : q ⬝ᵥ Matrix.mulVec (lowerBoxHessian x)⁻¹ q =
      x (upper o) ^ 2 + x (lower o) ^ 2 := by
    exact lowerBox_effectiveResistance x hx.1 o
  have hdetlower : 1 / x (lower o) ^ 2 ≤ (lowerBoxHessian x).det := by
    rw [lowerBoxHessian_det]
    rw [← Finset.mul_prod_erase Finset.univ (fun u => 1 / x u ^ 2)
      (Finset.mem_univ (lower o))]
    exact le_mul_of_one_le_right (by positivity)
      (Finset.one_le_prod fun u _ => lower_factor_one_le hx.1 u)
  have hRlower : x (lower o) ^ 2 ≤
      x (upper o) ^ 2 + x (lower o) ^ 2 := by
    nlinarith [sq_nonneg (x (upper o))]
  have hxlowerSq : 0 < x (lower o) ^ 2 := sq_pos_of_pos (hx.1 (lower o)).1
  have hdetR : 1 ≤ (lowerBoxHessian x).det *
      (x (upper o) ^ 2 + x (lower o) ^ 2) := by
    calc
      1 = (1 / x (lower o) ^ 2) * x (lower o) ^ 2 := by
        field_simp [ne_of_gt (hx.1 (lower o)).1]
      _ ≤ (lowerBoxHessian x).det *
          (x (upper o) ^ 2 + x (lower o) ^ 2) :=
        mul_le_mul hdetlower hRlower (sq_nonneg _) hD.det_pos.le
  have hdiv : 1 / s ^ 2 ≤
      ((lowerBoxHessian x).det *
        (x (upper o) ^ 2 + x (lower o) ^ 2)) / s ^ 2 := by
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hs)).2 hdetR
  have hbase : 1 / s ^ 2 ≤
      (lowerBoxHessian x + (BarrierRow.ofObservation o).hessianTerm x).det := by
    rw [hformula, hres]
    have hdetnonneg := hD.det_pos.le
    calc
      1 / s ^ 2 ≤ (lowerBoxHessian x).det *
          (x (upper o) ^ 2 + x (lower o) ^ 2) / s ^ 2 := hdiv
      _ ≤ (lowerBoxHessian x).det *
          (1 + (x (upper o) ^ 2 + x (lower o) ^ 2) / s ^ 2) := by
        calc
          (lowerBoxHessian x).det *
                (x (upper o) ^ 2 + x (lower o) ^ 2) / s ^ 2 =
              (lowerBoxHessian x).det *
                ((x (upper o) ^ 2 + x (lower o) ^ 2) / s ^ 2) := by ring
          _ ≤ (lowerBoxHessian x).det + (lowerBoxHessian x).det *
                ((x (upper o) ^ 2 + x (lower o) ^ 2) / s ^ 2) :=
            le_add_of_nonneg_left hdetnonneg
          _ = _ := by ring
  obtain ⟨remainder, heq, hrem⟩ :=
    barrierHessian_eq_lower_row_add_remainder (x := x) ho
  rw [heq]
  exact hbase.trans (det_le_det_add_of_posDef_of_posSemidef
    (hD.add_posSemidef (BarrierRow.hessianTerm_posSemidef _ _)) hrem)

private theorem exp_neg_le_of_inv_sq_det_le {h : History n}
    {x : Placement n} {s B : ℝ} (hx : InHistoryPolytope h x)
    (hs : 0 < s) (hdet : 1 / s ^ 2 ≤ (barrierHessian h x).det)
    (hvalue : volumetricValue h x ≤ B) :
    Real.exp (-B) ≤ s := by
  have hHdet : 0 < (barrierHessian h x).det := (barrierHessian_posDef hx).det_pos
  have hinv : 0 < 1 / s ^ 2 := div_pos zero_lt_one (sq_pos_of_pos hs)
  have hlog := Real.strictMonoOn_log.monotoneOn hinv hHdet hdet
  have hlogid : Real.log (1 / s ^ 2) = -2 * Real.log s := by
    rw [Real.log_div one_ne_zero (pow_ne_zero 2 hs.ne'), Real.log_one,
      Real.log_pow]
    ring
  have hB : -B ≤ Real.log s := by
    rw [volumetricValue] at hvalue
    rw [hlogid] at hlog
    nlinarith
  exact (Real.exp_le_exp.mpr hB).trans_eq (Real.exp_log hs)

theorem lower_coordinate_sublevel {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) {B : ℝ}
    (hvalue : volumetricValue h x ≤ B) (v : Item n) :
    Real.exp (-B) ≤ x v := by
  exact exp_neg_le_of_inv_sq_det_le hx (hx.1 v).1
    (lower_coordinate_det_le hx.1 v) hvalue

theorem upper_coordinate_sublevel {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) {B : ℝ}
    (hvalue : volumetricValue h x ≤ B) (v : Item n) :
    Real.exp (-B) ≤ 1 - x v := by
  exact exp_neg_le_of_inv_sq_det_le hx (sub_pos.2 (hx.1 v).2)
    (upper_coordinate_det_le hx.1 v) hvalue

theorem comparison_slack_sublevel {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) {B : ℝ}
    (hvalue : volumetricValue h x ≤ B) {o : Observation n} (ho : o ∈ h) :
    Real.exp (-B) ≤ (BarrierRow.ofObservation o).slack x := by
  have hs := (BarrierRow.realizesPlacement_iff_slack_pos o x).1
    ((List.forall_iff_forall_mem.1 hx.2) o ho)
  exact exp_neg_le_of_inv_sq_det_le hx hs
    (comparison_slack_det_le hx ho) hvalue

theorem continuousAt_barrierHessian {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) :
    ContinuousAt (barrierHessian h) x := by
  have hslacks := barrierRows_slack_pos hx
  have aux : ∀ rows : List (BarrierRow n),
      (∀ row ∈ rows, 0 < row.slack x) →
      ContinuousAt (fun y =>
        ((rows.map fun row => row.hessianTerm y).sum)) x := by
    intro rows hrows
    induction rows with
    | nil => exact continuousAt_const
    | cons row rows ih =>
        simp only [List.map_cons, List.sum_cons]
        apply ContinuousAt.add
        · change ContinuousAt (fun y => Matrix.of (fun u v =>
            row.normal u * row.normal v / row.slack y ^ 2)) x
          have hentries : ContinuousAt (fun y => fun u v =>
              row.normal u * row.normal v / row.slack y ^ 2) x := by
            rw [continuousAt_pi]
            intro u
            rw [continuousAt_pi]
            intro v
            have hslackContinuous : Continuous (fun y : Placement n => row.slack y) := by
              unfold BarrierRow.slack
              apply Continuous.sub
              · exact continuous_finsetSum _ fun w _ =>
                  continuous_const.mul (continuous_apply w)
              · exact continuous_const
            exact (continuousAt_const.mul continuousAt_const).div
              (hslackContinuous.continuousAt.pow 2)
              (pow_ne_zero 2 (ne_of_gt (hrows row (by simp))))
          exact hentries
        · exact ih (fun r hr => hrows r (by simp [hr]))
  unfold barrierHessian
  exact aux (barrierRows h) hslacks

theorem continuousAt_volumetricValue {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) :
    ContinuousAt (volumetricValue h) x := by
  have hdet : 0 < (barrierHessian h x).det := (barrierHessian_posDef hx).det_pos
  have hdetContinuous : ContinuousAt
      (fun y => (barrierHessian h y).det) x :=
    continuous_id.matrix_det.continuousAt.comp
      (continuousAt_barrierHessian hx)
  unfold volumetricValue
  exact continuousAt_const.mul
    (ContinuousAt.comp (x := x)
      (f := fun y => (barrierHessian h y).det)
      (Real.continuousAt_log hdet.ne') hdetContinuous)

theorem continuous_barrierRow_slack (row : BarrierRow n) :
    Continuous row.slack := by
  unfold BarrierRow.slack
  apply Continuous.sub
  · exact continuous_finsetSum _ fun v _ =>
      continuous_const.mul (continuous_apply v)
  · exact continuous_const

/-- Closed compact core containing the entire sublevel set at height `B`. -/
def centerCompactSet (h : History n) (B : ℝ) : Set (Placement n) :=
  {x | (∀ v, Real.exp (-B) ≤ x v ∧ x v ≤ 1 - Real.exp (-B)) ∧
    ∀ o ∈ h, Real.exp (-B) ≤ (BarrierRow.ofObservation o).slack x}

theorem centerCompactSet_isClosed (h : History n) (B : ℝ) :
    IsClosed (centerCompactSet h B) := by
  have hbox : IsClosed {x : Placement n |
      ∀ v, Real.exp (-B) ≤ x v ∧ x v ≤ 1 - Real.exp (-B)} := by
    rw [show {x : Placement n |
        ∀ v, Real.exp (-B) ≤ x v ∧ x v ≤ 1 - Real.exp (-B)} =
      ⋂ v, ({x | Real.exp (-B) ≤ x v} ∩
        {x | x v ≤ 1 - Real.exp (-B)}) by
      ext x
      simp]
    exact isClosed_iInter fun v =>
      (isClosed_le continuous_const (continuous_apply v)).inter
        (isClosed_le (continuous_apply v) continuous_const)
  have hobs : ∀ rows : History n,
      IsClosed {x : Placement n |
        ∀ o ∈ rows, Real.exp (-B) ≤ (BarrierRow.ofObservation o).slack x} := by
    intro rows
    induction rows with
    | nil => simp
    | cons o rows ih =>
        rw [show {x : Placement n |
            ∀ r ∈ o :: rows,
              Real.exp (-B) ≤ (BarrierRow.ofObservation r).slack x} =
          {x | Real.exp (-B) ≤ (BarrierRow.ofObservation o).slack x} ∩
            {x | ∀ r ∈ rows,
              Real.exp (-B) ≤ (BarrierRow.ofObservation r).slack x} by
          ext x
          simp]
        exact (isClosed_le continuous_const
          (continuous_barrierRow_slack _)).inter ih
  rw [show centerCompactSet h B =
      {x : Placement n |
        ∀ v, Real.exp (-B) ≤ x v ∧ x v ≤ 1 - Real.exp (-B)} ∩
      {x : Placement n |
        ∀ o ∈ h, Real.exp (-B) ≤ (BarrierRow.ofObservation o).slack x} by
    ext x
    rfl]
  exact hbox.inter (hobs h)

theorem centerCompactSet_subset_cube (h : History n) (B : ℝ) :
    centerCompactSet h B ⊆
      {x : Placement n | ∀ v, x v ∈ Set.Icc (0 : ℝ) 1} := by
  intro x hx v
  have heps : 0 < Real.exp (-B) := Real.exp_pos _
  exact ⟨heps.le.trans (hx.1 v).1,
    (hx.1 v).2.trans (sub_le_self _ heps.le)⟩

theorem centerCompactSet_isCompact (h : History n) (B : ℝ) :
    IsCompact (centerCompactSet h B) := by
  have hcube : IsCompact
      {x : Placement n | ∀ v, x v ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  exact hcube.of_isClosed_subset (centerCompactSet_isClosed h B)
    (centerCompactSet_subset_cube h B)

theorem centerCompactSet_subset_historyPolytope (h : History n) (B : ℝ) :
    centerCompactSet h B ⊆ {x | InHistoryPolytope h x} := by
  intro x hx
  have heps : 0 < Real.exp (-B) := Real.exp_pos _
  constructor
  · intro v
    exact ⟨heps.trans_le (hx.1 v).1,
      lt_of_le_of_lt (hx.1 v).2 (sub_lt_self _ heps)⟩
  · rw [List.forall_iff_forall_mem]
    intro o ho
    apply (BarrierRow.realizesPlacement_iff_slack_pos o x).2
    exact heps.trans_le (hx.2 o ho)

theorem mem_centerCompactSet_of_value_le {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) {B : ℝ}
    (hvalue : volumetricValue h x ≤ B) :
    x ∈ centerCompactSet h B := by
  constructor
  · intro v
    constructor
    · exact lower_coordinate_sublevel hx hvalue v
    · have hu := upper_coordinate_sublevel hx hvalue v
      linarith
  · intro o ho
    exact comparison_slack_sublevel hx hvalue ho

/-- Every feasible history has a genuine interior volumetric center. -/
theorem exists_volumetricCenter (h : History n) (hh : Feasible h) :
    ∃ x : Placement n, IsVolumetricCenter h x := by
  obtain ⟨π, hπ⟩ := hh
  let y := rankingPlacement π
  have hy : InHistoryPolytope h y := rankingPlacement_mem π h hπ
  let B := volumetricValue h y
  have hycore : y ∈ centerCompactSet h B :=
    mem_centerCompactSet_of_value_le hy (le_refl _)
  have hcompact := centerCompactSet_isCompact h B
  have hcontinuous : ContinuousOn (volumetricValue h) (centerCompactSet h B) := by
    intro z hz
    exact (continuousAt_volumetricValue
      (centerCompactSet_subset_historyPolytope h B hz)).continuousWithinAt
  obtain ⟨z, hz, hzmin⟩ := hcompact.exists_isMinOn ⟨y, hycore⟩ hcontinuous
  refine ⟨z, centerCompactSet_subset_historyPolytope h B hz, ?_⟩
  intro w hw
  by_cases hwB : volumetricValue h w ≤ B
  · exact hzmin (mem_centerCompactSet_of_value_le hw hwB)
  · have hzy : volumetricValue h z ≤ volumetricValue h y := hzmin hycore
    exact hzy.trans (lt_of_not_ge hwB).le

end StrengthenedCurvature
end SortingAdversary
