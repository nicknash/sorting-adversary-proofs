import SortingAdversary.StrengthenedCurvature.HistoryPolytope
import SortingAdversary.StrengthenedCurvature.InformativeHistory
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Logarithmic barrier and volumetric potential

This is the direct finite-dimensional translation of equations (1)--(4) in
the strengthened-curvature paper.  Every comparison row is retained, so the
state is genuinely history dependent.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- A strict affine inequality `normal ⬝ x > boundary`. -/
structure BarrierRow (n : ℕ) where
  normal : Item n → ℝ
  boundary : ℝ

namespace BarrierRow

private theorem sum_two_deltas {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (hab : a ≠ b) (f g : ι → ℝ) :
    (∑ i, if i = a then f i else if i = b then g i else 0) = f a + g b := by
  calc
    (∑ i, if i = a then f i else if i = b then g i else 0) =
        ∑ i, ((if i = a then f i else 0) + (if i = b then g i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hia : i = a
      · subst i
        simp [hab]
      · simp [hia]
    _ = f a + g b := by simp [Finset.sum_add_distrib]

/-- Slack of a barrier row at a placement. -/
def slack (row : BarrierRow n) (x : Placement n) : ℝ :=
  ∑ v, row.normal v * x v - row.boundary

/-- The rank-one Hessian contribution `aaᵀ/s²`. -/
noncomputable def hessianTerm (row : BarrierRow n) (x : Placement n) :
    Matrix (Item n) (Item n) ℝ :=
  fun u v => row.normal u * row.normal v / row.slack x ^ 2

/-- Every row contributes a positive-semidefinite rank-one matrix. -/
theorem hessianTerm_posSemidef (row : BarrierRow n) (x : Placement n) :
    (row.hessianTerm x).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext u v
    simp only [Matrix.conjTranspose_apply, starRingEnd_apply, star_trivial]
    simp [hessianTerm, mul_comm]
  · intro z
    have hsq : 0 ≤ (∑ u, z u * row.normal u) ^ 2 := sq_nonneg _
    have hden : 0 ≤ row.slack x ^ 2 := sq_nonneg _
    by_cases hs : row.slack x = 0
    · simp [dotProduct, Matrix.mulVec, hessianTerm, hs]
    · rw [show star z = z by ext u; simp]
      simp only [dotProduct, Matrix.mulVec, hessianTerm]
      rw [show (∑ u, z u * ∑ v, row.normal u * row.normal v /
          row.slack x ^ 2 * z v) =
          (∑ u, z u * row.normal u) ^ 2 / row.slack x ^ 2 by
        calc
          (∑ u, z u * ∑ v, row.normal u * row.normal v /
              row.slack x ^ 2 * z v) =
              ∑ u, (z u * row.normal u) *
                ((∑ v, z v * row.normal v) / row.slack x ^ 2) := by
            apply Finset.sum_congr rfl
            intro u _
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v _
            ring
          _ = (∑ u, z u * row.normal u) *
              ((∑ v, z v * row.normal v) / row.slack x ^ 2) := by
            rw [Finset.sum_mul]
          _ = (∑ u, z u * row.normal u) ^ 2 / row.slack x ^ 2 := by
            ring]
      exact div_nonneg hsq hden

/-- Lower box row `x_v > 0`. -/
def lowerBox (v : Item n) : BarrierRow n where
  normal := fun u => if u = v then 1 else 0
  boundary := 0

/-- Upper box row `-x_v > -1`. -/
def upperBox (v : Item n) : BarrierRow n where
  normal := fun u => if u = v then -1 else 0
  boundary := -1

/-- The oriented row contributed by an answered comparison. -/
def ofObservation (o : Observation n) : BarrierRow n where
  normal := match o.answer with
    | .less => fun v =>
        if v = o.query.right then 1 else if v = o.query.left then -1 else 0
    | .greater => fun v =>
        if v = o.query.left then 1 else if v = o.query.right then -1 else 0
  boundary := 0

@[simp] theorem slack_lowerBox (v : Item n) (x : Placement n) :
    (lowerBox v).slack x = x v := by
  classical
  simp [slack, lowerBox]

@[simp] theorem slack_upperBox (v : Item n) (x : Placement n) :
    (upperBox v).slack x = 1 - x v := by
  classical
  simp [slack, upperBox]
  ring

@[simp] theorem slack_ofObservation_less (q : Query n) (x : Placement n) :
    (ofObservation ⟨q, .less⟩).slack x = x q.right - x q.left := by
  classical
  unfold slack ofObservation
  simp only [ite_mul, one_mul, neg_one_mul, zero_mul, sub_zero]
  rw [sum_two_deltas q.right q.left q.distinct.symm x (fun v => -x v)]
  ring

@[simp] theorem slack_ofObservation_greater (q : Query n) (x : Placement n) :
    (ofObservation ⟨q, .greater⟩).slack x = x q.left - x q.right := by
  classical
  unfold slack ofObservation
  simp only [ite_mul, one_mul, neg_one_mul, zero_mul, sub_zero]
  rw [sum_two_deltas q.left q.right q.distinct x (fun v => -x v)]
  ring

theorem realizesPlacement_iff_slack_pos (o : Observation n) (x : Placement n) :
    RealizesPlacement o x ↔ 0 < (ofObservation o).slack x := by
  cases o with
  | mk q answer =>
      cases answer <;> simp [RealizesPlacement, sub_pos]

theorem ofObservation_normal_eq (o : Observation n) (v : Item n) :
    (ofObservation o).normal v =
      if v = upper o then 1 else if v = lower o then -1 else 0 := by
  cases o with
  | mk q answer => cases answer <;> rfl

theorem slack_ofObservation_eq (o : Observation n) (x : Placement n) :
    (ofObservation o).slack x = x (upper o) - x (lower o) := by
  cases o with
  | mk q answer => cases answer <;> simp [lower, upper]

theorem lower_ne_upper (o : Observation n) : lower o ≠ upper o := by
  cases o with
  | mk q answer =>
      cases answer
      · exact q.distinct
      · exact q.distinct.symm

theorem ofObservation_normal_ne_zero (o : Observation n) :
    (ofObservation o).normal ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (upper o)
  simp [ofObservation_normal_eq, lower_ne_upper o] at hvalue

end BarrierRow

/-- The two ground-boundary rows for each item. -/
def boxRows (n : ℕ) : List (BarrierRow n) :=
  (List.ofFn fun v : Item n => BarrierRow.lowerBox v) ++
    (List.ofFn fun v : Item n => BarrierRow.upperBox v)

/-- Every barrier row retained by a history. -/
def barrierRows (h : History n) : List (BarrierRow n) :=
  boxRows n ++ h.map BarrierRow.ofObservation

/-- The logarithmic-barrier Hessian from equation (2). -/
noncomputable def barrierHessian (h : History n) (x : Placement n) :
    Matrix (Item n) (Item n) ℝ :=
  ((barrierRows h).map fun row => row.hessianTerm x).sum

/-- The contribution of the lower ground rows. -/
noncomputable def lowerBoxHessian (x : Placement n) :
    Matrix (Item n) (Item n) ℝ :=
  ((List.ofFn fun v : Item n => BarrierRow.lowerBox v).map
    fun row => row.hessianTerm x).sum

/-- The contribution of the upper ground rows. -/
noncomputable def upperBoxHessian (x : Placement n) :
    Matrix (Item n) (Item n) ℝ :=
  ((List.ofFn fun v : Item n => BarrierRow.upperBox v).map
    fun row => row.hessianTerm x).sum

theorem lowerBoxHessian_eq_diagonal (x : Placement n) :
    lowerBoxHessian x = Matrix.diagonal fun v => 1 / x v ^ 2 := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    rw [lowerBoxHessian, List.map_ofFn, List.sum_ofFn, Matrix.sum_apply]
    simp [Function.comp_apply, BarrierRow.hessianTerm, BarrierRow.lowerBox,
      BarrierRow.slack, Matrix.diagonal]
    rw [Finset.sum_eq_single u] <;> simp
    intro b hbu
    exact Or.inl fun hub => hbu hub.symm
  · rw [lowerBoxHessian, List.map_ofFn, List.sum_ofFn, Matrix.sum_apply]
    simp [Function.comp_apply, BarrierRow.hessianTerm, BarrierRow.lowerBox,
      BarrierRow.slack, Matrix.diagonal, huv]
    rw [Finset.sum_eq_single v] <;> simp [huv]
    intro b hb
    exact Or.inl fun hvb => by subst b; exact huv

theorem lowerBoxHessian_posDef {x : Placement n} (hx : InUnitBox x) :
    (lowerBoxHessian x).PosDef := by
  rw [lowerBoxHessian_eq_diagonal]
  exact Matrix.PosDef.diagonal fun v => div_pos zero_lt_one (sq_pos_of_pos (hx v).1)

theorem upperBoxHessian_eq_diagonal (x : Placement n) :
    upperBoxHessian x = Matrix.diagonal fun v => 1 / (1 - x v) ^ 2 := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    rw [upperBoxHessian, List.map_ofFn, List.sum_ofFn, Matrix.sum_apply]
    simp [Function.comp_apply, BarrierRow.hessianTerm, BarrierRow.upperBox,
      BarrierRow.slack, Matrix.diagonal]
    rw [Finset.sum_eq_single u] <;> simp
    ring
    intro b hbu
    exact Or.inl fun hub => hbu hub.symm
  · rw [upperBoxHessian, List.map_ofFn, List.sum_ofFn, Matrix.sum_apply]
    simp [Function.comp_apply, BarrierRow.hessianTerm, BarrierRow.upperBox,
      BarrierRow.slack, Matrix.diagonal, huv]
    rw [Finset.sum_eq_single v] <;> simp [huv]
    intro b hb
    exact Or.inl fun hvb => by subst b; exact huv

theorem upperBoxHessian_posDef {x : Placement n} (hx : InUnitBox x) :
    (upperBoxHessian x).PosDef := by
  rw [upperBoxHessian_eq_diagonal]
  exact Matrix.PosDef.diagonal fun v =>
    div_pos zero_lt_one (sq_pos_of_pos (sub_pos.2 (hx v).2))

theorem barrierHessian_nil_eq_diagonal (x : Placement n) :
    barrierHessian ([] : History n) x =
      Matrix.diagonal fun v => 1 / x v ^ 2 + 1 / (1 - x v) ^ 2 := by
  rw [show barrierHessian ([] : History n) x =
      lowerBoxHessian x + upperBoxHessian x by
    simp [barrierHessian, barrierRows, boxRows, lowerBoxHessian,
      upperBoxHessian, List.sum_append]]
  rw [lowerBoxHessian_eq_diagonal, upperBoxHessian_eq_diagonal]
  ext u v
  by_cases huv : u = v <;> simp [Matrix.diagonal, huv]

theorem hessianTerms_posSemidef (rows : List (BarrierRow n))
    (x : Placement n) :
    ((rows.map fun row => BarrierRow.hessianTerm row x).sum).PosSemidef := by
  induction rows with
  | nil => simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Item n) (Item n) ℝ).PosSemidef)
  | cons row rows ih =>
      simpa using (row.hessianTerm_posSemidef x).add ih

/-- Split the full Hessian into its positive-definite lower-box diagonal and
the positive-semidefinite contribution of every remaining row. -/
theorem barrierHessian_eq_lower_add (h : History n) (x : Placement n) :
    barrierHessian h x = lowerBoxHessian x +
      ((((List.ofFn fun v : Item n => BarrierRow.upperBox v) ++
          h.map BarrierRow.ofObservation).map fun row => row.hessianTerm x).sum) := by
  simp [barrierHessian, barrierRows, boxRows, lowerBoxHessian,
    List.sum_append, add_assoc]

/-- The symmetric decomposition using the upper-box diagonal. -/
theorem barrierHessian_eq_upper_add (h : History n) (x : Placement n) :
    barrierHessian h x = upperBoxHessian x +
      ((((List.ofFn fun v : Item n => BarrierRow.lowerBox v) ++
          h.map BarrierRow.ofObservation).map fun row => row.hessianTerm x).sum) := by
  simp [barrierHessian, barrierRows, boxRows, upperBoxHessian,
    List.sum_append, add_comm, add_left_comm, add_assoc]

/-- The box rows make the barrier Hessian positive definite at every feasible
point, independently of the comparison history. -/
theorem barrierHessian_posDef {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) :
    (barrierHessian h x).PosDef := by
  rw [barrierHessian_eq_lower_add]
  exact (lowerBoxHessian_posDef hx.1).add_posSemidef
    (hessianTerms_posSemidef _ x)

/-- Natural-log volumetric value `1/2 ln det H`. -/
noncomputable def volumetricValue (h : History n) (x : Placement n) : ℝ :=
  (1 / 2 : ℝ) * Real.log (barrierHessian h x).det

/-- Base-two volumetric value used for comparison accounting. -/
noncomputable def volumetricValue₂ (h : History n) (x : Placement n) : ℝ :=
  volumetricValue h x / Real.log 2

/-- The optimized history potential from equation (4), expressed as an
infimum so that the definition does not conceal a choice of center. -/
noncomputable def historyPotential (h : History n) : ℝ :=
  sInf (volumetricValue₂ h '' {x | InHistoryPolytope h x})

theorem barrierRows_slack_pos {h : History n} {x : Placement n}
    (hx : InHistoryPolytope h x) :
    ∀ row ∈ barrierRows h, 0 < row.slack x := by
  intro row hrow
  rcases List.mem_append.1 hrow with hbox | hobs
  · rcases List.mem_append.1 hbox with hlower | hupper
    · obtain ⟨v, rfl⟩ := List.mem_ofFn.1 hlower
      simpa using (hx.1 v).1
    · obtain ⟨v, rfl⟩ := List.mem_ofFn.1 hupper
      simpa [sub_pos] using (hx.1 v).2
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hobs
    exact (BarrierRow.realizesPlacement_iff_slack_pos o x).1
      ((List.forall_iff_forall_mem.1 hx.2) o ho)

end StrengthenedCurvature
end SortingAdversary
