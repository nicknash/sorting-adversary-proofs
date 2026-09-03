import SortingAdversary.StrengthenedCurvature.AugmentedCurvature
import SortingAdversary.StrengthenedCurvature.HistoryFeasibility
import SortingAdversary.StrengthenedCurvature.Whitening
import Mathlib.Tactic.FieldSimp

/-!
# The augmented Gram curve for one retained comparison

This module identifies the generic row-scaled Gram curve with the old barrier
Hessian along the electrical line plus the fixed prospective query row.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open scoped BigOperators

variable {n : ℕ}

abbrev OldRowIndex (h : History n) := Fin (barrierRows h).length

def indexedBarrierRow (h : History n) (i : OldRowIndex h) : BarrierRow n :=
  (barrierRows h).get i

noncomputable def normalizedOldRows (h : History n) (x : Placement n) :
    Matrix (OldRowIndex h) (Item n) ℝ :=
  fun i v => (indexedBarrierRow h i).normal v / (indexedBarrierRow h i).slack x

noncomputable def augmentedRows (h : History n) (x : Placement n)
    (o : Observation n) (t : ℝ) :
    Matrix (Option (OldRowIndex h)) (Item n) ℝ
  | none, v => (BarrierRow.ofObservation o).normal v /
      (Real.sqrt (effectiveResistance h x o) * t)
  | some i, v => normalizedOldRows h x i v

noncomputable def augmentedMotions (h : History n) (x : Placement n)
    (o : Observation n) : Option (OldRowIndex h) → ℝ
  | none => 0
  | some i => electricalMotion h x o (indexedBarrierRow h i)

noncomputable def electricalLine (h : History n) (x : Placement n)
    (o : Observation n) (s : ℝ) : Placement n :=
  x + s • electricalDirection h x o

theorem columnGram_normalizedOldRows_eq (h : History n) (x : Placement n) :
    columnGram (normalizedOldRows h x) = barrierHessian h x := by
  classical
  ext u v
  unfold columnGram
  rw [Matrix.mul_apply]
  change (∑ i : OldRowIndex h,
      (indexedBarrierRow h i).normal u / (indexedBarrierRow h i).slack x *
        ((indexedBarrierRow h i).normal v / (indexedBarrierRow h i).slack x)) = _
  have hrows :
      ((barrierRows h).map fun row => row.hessianTerm x) =
        List.ofFn (fun i : OldRowIndex h => (indexedBarrierRow h i).hessianTerm x) := by
    symm
    change List.ofFn (fun i : Fin (barrierRows h).length =>
      ((barrierRows h).get i).hessianTerm x) = _
    calc
      _ = (List.ofFn (barrierRows h).get).map (fun row => row.hessianTerm x) :=
        List.ofFn_comp' (barrierRows h).get (fun row => row.hessianTerm x)
      _ = _ := by rw [List.ofFn_get]
  rw [barrierHessian, hrows, List.sum_ofFn, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [BarrierRow.hessianTerm]
  ring

/-- Positivity of every retained barrier slack is also sufficient for
membership in the strict history polytope. -/
theorem inHistoryPolytope_of_barrierRows_slack_pos (h : History n)
    (x : Placement n)
    (hrows : ∀ row ∈ barrierRows h, 0 < row.slack x) :
    InHistoryPolytope h x := by
  constructor
  · intro v
    constructor
    · simpa using hrows (BarrierRow.lowerBox v) (by
        simp [barrierRows, boxRows])
    · have hu := hrows (BarrierRow.upperBox v) (by
        simp [barrierRows, boxRows])
      simpa [sub_pos] using hu
  · rw [List.forall_iff_forall_mem]
    intro o ho
    rw [BarrierRow.realizesPlacement_iff_slack_pos]
    exact hrows (BarrierRow.ofObservation o) (by
      rw [barrierRows]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))

/-- Every old slack changes by its normalized electrical motion. -/
theorem electricalLine_slack {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (row : BarrierRow n) (hrow : row ∈ barrierRows h) (s : ℝ) :
    row.slack (electricalLine h x o s) =
      row.slack x * (1 + s * electricalMotion h x o row) := by
  have hslack : row.slack x ≠ 0 :=
    ne_of_gt (barrierRows_slack_pos hx row hrow)
  rw [electricalLine, row.slack_line]
  unfold electricalMotion normalizedRowMotion
  field_simp [hslack]

/-- The open unit electrical segment preserves all old inequalities. -/
theorem electricalLine_mem {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) {s : ℝ}
    (hs : |s| < 1) : InHistoryPolytope h (electricalLine h x o s) := by
  apply inHistoryPolytope_of_barrierRows_slack_pos h
  intro row hrow
  rw [electricalLine_slack hx o row hrow s]
  apply mul_pos (barrierRows_slack_pos hx row hrow)
  have hmotion := abs_electricalMotion_le_one hx o hrow
  have hproduct : |s * electricalMotion h x o row| < 1 := by
    rw [abs_mul]
    calc
      |s| * |electricalMotion h x o row| ≤ |s| * 1 :=
        mul_le_mul_of_nonneg_left hmotion (abs_nonneg s)
      _ < 1 := by simpa using hs
  linarith [neg_lt_of_abs_lt hproduct]

/-- The queried normal advances by exactly one normalized resistance unit
along the electrical direction. -/
theorem query_directionalSlack_electricalDirection {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n) :
    (BarrierRow.ofObservation o).directionalSlack
        (electricalDirection h x o) =
      Real.sqrt (effectiveResistance h x o) := by
  have hR : 0 < effectiveResistance h x o := effectiveResistance_pos hx o
  have hsqrt : 0 < Real.sqrt (effectiveResistance h x o) := Real.sqrt_pos.2 hR
  have hsquare : Real.sqrt (effectiveResistance h x o) ^ 2 =
      effectiveResistance h x o := Real.sq_sqrt hR.le
  unfold BarrierRow.directionalSlack electricalDirection
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, (BarrierRow.ofObservation o).normal i *
        ((Real.sqrt (effectiveResistance h x o))⁻¹ *
          Matrix.mulVec (barrierHessian h x)⁻¹
            (BarrierRow.ofObservation o).normal i)) =
        (Real.sqrt (effectiveResistance h x o))⁻¹ *
          effectiveResistance h x o := by
      simp only [effectiveResistance, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = Real.sqrt (effectiveResistance h x o) := by
      field_simp [hsqrt.ne']
      nlinarith

/-- Affine query-slack identity, equation (15) of the note. -/
theorem query_slack_electricalLine {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) (s : ℝ) :
    (BarrierRow.ofObservation o).slack (electricalLine h x o s) =
      (BarrierRow.ofObservation o).slack x +
        s * Real.sqrt (effectiveResistance h x o) := by
  rw [electricalLine, BarrierRow.slack_line,
    query_directionalSlack_electricalDirection hx o]

def oppositeAnswer : Answer → Answer
  | .less => .greater
  | .greater => .less

def oppositeObservation (o : Observation n) : Observation n :=
  ⟨o.query, oppositeAnswer o.answer⟩

@[simp] theorem oppositeObservation_normal (o : Observation n) :
    (BarrierRow.ofObservation (oppositeObservation o)).normal =
      -(BarrierRow.ofObservation o).normal := by
  ext v
  cases o with
  | mk q answer =>
      cases answer <;> simp [oppositeObservation, oppositeAnswer,
        BarrierRow.ofObservation]
      all_goals by_cases hleft : v = q.left <;>
        by_cases hright : v = q.right <;>
          simp [hleft, hright, q.distinct, q.distinct.symm]

@[simp] theorem oppositeObservation_slack (o : Observation n) (x : Placement n) :
    (BarrierRow.ofObservation (oppositeObservation o)).slack x =
      -(BarrierRow.ofObservation o).slack x := by
  cases o with
  | mk q answer => cases answer <;> simp [oppositeObservation, oppositeAnswer]

/-- Orient a query so that its slack at the old center is nonnegative. -/
noncomputable def centerOrientation (x : Placement n) (q : Query n) : Observation n :=
  if x q.left ≤ x q.right then ⟨q, .less⟩ else ⟨q, .greater⟩

@[simp] theorem centerOrientation_query (x : Placement n) (q : Query n) :
    (centerOrientation x q).query = q := by
  unfold centerOrientation
  split <;> rfl

@[simp] theorem oppositeObservation_query (o : Observation n) :
    (oppositeObservation o).query = o.query := rfl

@[simp] theorem observation_mk_query_answer (o : Observation n) :
    Observation.mk o.query o.answer = o := by cases o; rfl

theorem centerOrientation_slack_nonneg (x : Placement n) (q : Query n) :
    0 ≤ (BarrierRow.ofObservation (centerOrientation x q)).slack x := by
  unfold centerOrientation
  split_ifs with h
  · simp
    linarith
  · simp
    exact (lt_of_not_ge h).le

/-- Normalized signed distance of the old center from the query hyperplane. -/
noncomputable def queryOffset (h : History n) (x : Placement n)
    (o : Observation n) : ℝ :=
  (BarrierRow.ofObservation o).slack x /
    Real.sqrt (effectiveResistance h x o)

theorem queryOffset_nonneg {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) {o : Observation n}
    (ho : 0 ≤ (BarrierRow.ofObservation o).slack x) :
    0 ≤ queryOffset h x o := by
  exact div_nonneg ho (Real.sqrt_nonneg _)

theorem query_slack_eq_sqrt_mul_offset {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) :
    (BarrierRow.ofObservation o).slack x =
      Real.sqrt (effectiveResistance h x o) * queryOffset h x o := by
  have hsqrt : Real.sqrt (effectiveResistance h x o) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (effectiveResistance_pos hx o))
  unfold queryOffset
  field_simp

theorem query_slack_electricalLine_offset {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) (s : ℝ) :
    (BarrierRow.ofObservation o).slack (electricalLine h x o s) =
      Real.sqrt (effectiveResistance h x o) * (queryOffset h x o + s) := by
  rw [query_slack_electricalLine hx o, query_slack_eq_sqrt_mul_offset hx o]
  ring

theorem opposite_query_slack_electricalLine_offset {h : History n}
    {x : Placement n} (hx : InHistoryPolytope h x) (o : Observation n) (s : ℝ) :
    (BarrierRow.ofObservation (oppositeObservation o)).slack
        (electricalLine h x o s) =
      -Real.sqrt (effectiveResistance h x o) * (queryOffset h x o + s) := by
  rw [oppositeObservation_slack, query_slack_electricalLine_offset hx o]
  ring

theorem electrical_rowDenominator_pos {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (row : BarrierRow n) (hrow : row ∈ barrierRows h) {s : ℝ}
    (hs : |s| < 1) : 0 < 1 + s * electricalMotion h x o row := by
  have hmotion := abs_electricalMotion_le_one hx o hrow
  have hproduct : |s * electricalMotion h x o row| < 1 := by
    rw [abs_mul]
    calc
      |s| * |electricalMotion h x o row| ≤ |s| * 1 :=
        mul_le_mul_of_nonneg_left hmotion (abs_nonneg s)
      _ < 1 := by simpa using hs
  linarith [neg_lt_of_abs_lt hproduct]

theorem augmented_rowDenominator_ne {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) {s : ℝ}
    (hs : |s| < 1) :
    ∀ i, rowDenominator (augmentedMotions h x o) s i ≠ 0 := by
  intro i
  cases i with
  | none => simp [rowDenominator, augmentedMotions]
  | some i =>
      exact ne_of_gt (by
        simpa [rowDenominator, augmentedMotions] using
          electrical_rowDenominator_pos hx o (indexedBarrierRow h i)
            (List.get_mem (barrierRows h) i) hs)

theorem scaledRows_augmented_some {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) (t s : ℝ)
    (hs : |s| < 1) (i : OldRowIndex h) (v : Item n) :
    scaledRows (augmentedRows h x o t) (augmentedMotions h x o) s (some i) v =
      normalizedOldRows h (electricalLine h x o s) i v := by
  have hrow : indexedBarrierRow h i ∈ barrierRows h :=
    List.get_mem (barrierRows h) i
  have hold : (indexedBarrierRow h i).slack x ≠ 0 :=
    ne_of_gt (barrierRows_slack_pos hx _ hrow)
  have hfactor : 1 + s * electricalMotion h x o (indexedBarrierRow h i) ≠ 0 :=
    ne_of_gt (electrical_rowDenominator_pos hx o _ hrow hs)
  unfold normalizedOldRows
  rw [electricalLine_slack hx o _ hrow]
  unfold scaledRows augmentedRows augmentedMotions rowDenominator
  unfold normalizedOldRows
  field_simp [hold, hfactor]

@[simp] theorem scaledRows_augmented_none (h : History n) (x : Placement n)
    (o : Observation n) (t s : ℝ) (v : Item n) :
    scaledRows (augmentedRows h x o t) (augmentedMotions h x o) s none v =
      (BarrierRow.ofObservation o).normal v /
        (Real.sqrt (effectiveResistance h x o) * t) := by
  simp [scaledRows, augmentedRows, augmentedMotions, rowDenominator]

/-- The abstract augmented Gram curve is the old Hessian along the electrical
line plus the fixed, resistance-normalized query rank-one term. -/
theorem scaledGram_augmented_eq {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) (t : ℝ) {s : ℝ}
    (hs : |s| < 1) :
    scaledGram (augmentedRows h x o t) (augmentedMotions h x o) s =
      barrierHessian h (electricalLine h x o s) +
        scaledRankOne (BarrierRow.ofObservation o).normal
          (Real.sqrt (effectiveResistance h x o) * t) := by
  classical
  ext u v
  simp only [scaledGram, columnGram, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.add_apply, scaledRankOne]
  rw [Fintype.sum_option]
  simp_rw [scaledRows_augmented_none]
  simp_rw [scaledRows_augmented_some hx o t s hs]
  have holdGram := congrArg (fun M : Matrix (Item n) (Item n) ℝ => M u v)
    (columnGram_normalizedOldRows_eq h (electricalLine h x o s))
  simp only [columnGram, Matrix.mul_apply, Matrix.transpose_apply] at holdGram
  rw [holdGram]
  ring

theorem scaledGram_augmented_posDef {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) (t : ℝ) {s : ℝ}
    (hs : |s| < 1) :
    (scaledGram (augmentedRows h x o t) (augmentedMotions h x o) s).PosDef := by
  rw [scaledGram_augmented_eq hx o t hs]
  exact (barrierHessian_posDef (electricalLine_mem hx o hs)).add_posSemidef
    (scaledRankOne_posSemidef _ _)

theorem scaledGram_augmented_det_pos {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) (t : ℝ) {s : ℝ}
    (hs : |s| < 1) :
    0 < (scaledGram (augmentedRows h x o t) (augmentedMotions h x o) s).det :=
  (scaledGram_augmented_posDef hx o t hs).det_pos

/-- Equation (18): at the old center the augmented query multiplies the
determinant by `1 + t⁻²`. -/
theorem scaledGram_augmented_det_zero {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) {t : ℝ} (ht : t ≠ 0) :
    (scaledGram (augmentedRows h x o t) (augmentedMotions h x o) 0).det =
      (barrierHessian h x).det * (1 + 1 / t ^ 2) := by
  have hR : 0 < effectiveResistance h x o := effectiveResistance_pos hx o
  have hsqrt : 0 < Real.sqrt (effectiveResistance h x o) := Real.sqrt_pos.2 hR
  rw [scaledGram_augmented_eq hx o t (by norm_num)]
  simp only [electricalLine, zero_smul, add_zero]
  rw [det_add_rankOne _ (barrierHessian_posDef hx)]
  · rw [show (BarrierRow.ofObservation o).normal ⬝ᵥ
          Matrix.mulVec (barrierHessian h x)⁻¹
            (BarrierRow.ofObservation o).normal =
        effectiveResistance h x o by rfl]
    have hquot : effectiveResistance h x o /
          (Real.sqrt (effectiveResistance h x o) * t) ^ 2 = 1 / t ^ 2 := by
      calc
        effectiveResistance h x o /
              (Real.sqrt (effectiveResistance h x o) * t) ^ 2 =
            Real.sqrt (effectiveResistance h x o) ^ 2 /
              (Real.sqrt (effectiveResistance h x o) * t) ^ 2 := by
                congr 1
                exact (Real.sq_sqrt hR.le).symm
        _ = 1 / t ^ 2 := by field_simp [hsqrt.ne', ht]
    rw [hquot]
  · exact mul_ne_zero hsqrt.ne' ht

/-- The positive electrical endpoint is an explicit feasible point of the
branch oriented at the old center. -/
theorem positiveTrial_mem {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (ho : 0 ≤ (BarrierRow.ofObservation o).slack x) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    InHistoryPolytope (o :: h) (electricalLine h x o a) := by
  have haabs : |a| < 1 := by simpa [abs_of_pos ha0] using ha1
  have hold := electricalLine_mem hx o haabs
  have hdelta := queryOffset_nonneg hx ho
  have hsqrt := Real.sqrt_pos.2 (effectiveResistance_pos hx o)
  have hquery : RealizesPlacement o (electricalLine h x o a) := by
    rw [BarrierRow.realizesPlacement_iff_slack_pos,
      query_slack_electricalLine_offset hx o]
    exact mul_pos hsqrt (add_pos_of_nonneg_of_pos hdelta ha0)
  exact ⟨hold.1, by simpa using And.intro hquery hold.2⟩

/-- The reflected endpoint is feasible when it crosses the query hyperplane. -/
theorem negativeTrial_mem {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hcross : queryOffset h x o < b) :
    InHistoryPolytope (oppositeObservation o :: h)
      (electricalLine h x o (-b)) := by
  have hbabs : |-b| < 1 := by simpa [abs_of_pos hb0] using hb1
  have hold := electricalLine_mem hx o hbabs
  have hsqrt := Real.sqrt_pos.2 (effectiveResistance_pos hx o)
  have hquery : RealizesPlacement (oppositeObservation o)
      (electricalLine h x o (-b)) := by
    rw [BarrierRow.realizesPlacement_iff_slack_pos,
      opposite_query_slack_electricalLine_offset hx o]
    nlinarith
  exact ⟨hold.1, by simpa using And.intro hquery hold.2⟩

theorem positiveTrial_feasible {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    (ho : 0 ≤ (BarrierRow.ofObservation o).slack x) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) : Feasible (o :: h) :=
  feasible_of_mem_historyPolytope (positiveTrial_mem hx o ho ha0 ha1)

theorem negativeTrial_feasible {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hcross : queryOffset h x o < b) :
    Feasible (oppositeObservation o :: h) :=
  feasible_of_mem_historyPolytope (negativeTrial_mem hx o hb0 hb1 hcross)

/-- At the positive endpoint the abstract Gram curve is exactly the child
barrier Hessian. -/
theorem scaledGram_positiveTrial {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    scaledGram (augmentedRows h x o (queryOffset h x o + a))
        (augmentedMotions h x o) a =
      barrierHessian (o :: h) (electricalLine h x o a) := by
  have haabs : |a| < 1 := by simpa [abs_of_pos ha0] using ha1
  rw [scaledGram_augmented_eq hx o _ haabs, barrierHessian_cons]
  congr 1
  ext u v
  simp only [scaledRankOne, BarrierRow.hessianTerm]
  rw [query_slack_electricalLine_offset hx o]

/-- At the negative endpoint the same curve is exactly the Hessian of the
oppositely oriented child. -/
theorem scaledGram_negativeTrial {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) (o : Observation n) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) :
    scaledGram (augmentedRows h x o (b - queryOffset h x o))
        (augmentedMotions h x o) (-b) =
      barrierHessian (oppositeObservation o :: h)
        (electricalLine h x o (-b)) := by
  have hbabs : |-b| < 1 := by simpa [abs_of_pos hb0] using hb1
  rw [scaledGram_augmented_eq hx o _ hbabs, barrierHessian_cons]
  congr 1
  ext u v
  simp only [scaledRankOne, BarrierRow.hessianTerm,
    oppositeObservation_normal, Pi.neg_apply]
  rw [opposite_query_slack_electricalLine_offset hx o]
  ring

end StrengthenedCurvature
end SortingAdversary
