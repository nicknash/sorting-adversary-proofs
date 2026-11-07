import SortingAdversary.Optimal.Reindexing
import SortingAdversary.Optimal.IdealCounting
import SortingAdversary.Optimal.NumericalRepresentation
import SortingAdversary.Optimal.Materialize

/-!
# Executable local comparison and CDF oracles

These routines call the materialized ideal-state dynamic program on the
actual sparse balls. The finite map enumerators occur only in correctness
statements. Original globally propagated endpoints come from the persistent
source partition's numerical view, and its exact law identity transfers every
error guarantee to the real parent pool.
-/

namespace SortingAdversary.Optimal.LocalOracle

open WeakMaps WeakMaps.WeakSystem LocalChoice MarginalCalibration
open GraphBalls CouplingHistory SparseClosure NumericalRepresentation
open IsolatedAccuracy TruncatedLaw

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- Exact weak-event ratio, evaluated by two materialized ideal-state DPs. -/
def branchEstimate (S : WeakSystem α K) (x y : α) : ℚ :=
  (IdealCounting.count (S.addRow x y) : ℚ) / IdealCounting.count S

theorem branchEstimate_eq (S : WeakSystem α K) (x y : α) :
    branchEstimate S x y = weakProbability S x y := by
  simp only [branchEstimate, IdealCounting.count_eq, weakProbability]

/-- Add a unary upper threshold. The endpoint is clipped only to the finite
palette ceiling; original upper bounds remain enforced by the minimum. -/
def ceilingSystem (S : WeakSystem α (K + 1)) (x : α) (c : ℕ) : WeakSystem α (K + 1) where
  edge := S.edge
  lower := S.lower
  upper y := if y = x then min (S.upper y) ⟨min c K, (min_le_right c K).trans_lt (Nat.lt_succ_self K)⟩
    else S.upper y

omit [Fintype α] in
theorem valid_ceilingSystem (S : WeakSystem α (K + 1)) (x : α) (c : ℕ) (f : ColorMap α (K + 1)) :
    (ceilingSystem S x c).Valid f ↔ S.Valid f ∧ (f x).val ≤ c := by
  constructor
  · rintro ⟨hw, hr⟩
    have hx : f x ≤ min (S.upper x)
        (⟨min c K, (min_le_right c K).trans_lt (Nat.lt_succ_self K)⟩ : Fin (K + 1)) := by
      simpa only [ceilingSystem, ite_true] using (hw x).2
    have hx' := le_min_iff.mp hx
    refine ⟨⟨?_, hr⟩, ?_⟩
    · intro y
      by_cases hy : y = x
      · subst y
        exact ⟨(hw x).1, hx'.1⟩
      · simpa only [ceilingSystem, if_neg hy] using hw y
    · exact (show (f x).val ≤ min c K from hx'.2).trans (min_le_left c K)
  · rintro ⟨⟨hw, hr⟩, hc⟩
    refine ⟨?_, hr⟩
    intro y
    by_cases hy : y = x
    · subst y
      refine ⟨(hw x).1, ?_⟩
      have hc' : f x ≤ (⟨min c K,
          (min_le_right c K).trans_lt (Nat.lt_succ_self K)⟩ : Fin (K + 1)) :=
        le_min hc (Nat.le_of_lt_succ (f x).isLt)
      simpa only [ceilingSystem, ite_true] using le_min (hw x).2 hc'
    · simpa only [ceilingSystem, if_neg hy] using hw y

theorem maps_ceilingSystem (S : WeakSystem α (K + 1)) (x : α) (c : ℕ) :
    (ceilingSystem S x c).maps = S.maps.filter (fun f => (f x).val ≤ c) := by
  ext f
  simp only [WeakSystem.mem_maps, valid_ceilingSystem, Finset.mem_filter]

/-- Exact numerator for the exclusive CDF; zero is handled without inventing
a palette value below its first color. -/
def cdfCount (S : WeakSystem α (K + 1)) (x : α) : ℕ → ℕ
  | 0 => 0
  | c + 1 => IdealCounting.count (ceilingSystem S x c)

theorem cdfCount_eq (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    cdfCount S x cut = (S.maps.filter (fun f => (f x).val < cut)).card := by
  cases cut with
  | zero => simp [cdfCount]
  | succ c =>
    simp only [cdfCount, IdealCounting.count_eq, WeakSystem.count, maps_ceilingSystem,
      Nat.lt_succ_iff]

/-- Exact CDF ratio, evaluated by materialized dynamic programming. -/
def cdfEstimate (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) : ℚ :=
  (cdfCount S x cut : ℚ) / IdealCounting.count S

theorem cdfEstimate_eq (S : WeakSystem α (K + 1)) (x : α) (cut : ℕ) :
    cdfEstimate S x cut = MarginalCalibration.cdf S x cut := by
  rw [cdfEstimate, cdfCount_eq, IdealCounting.count_eq, cdf_eq_card]

end Counting

variable {n K : ℕ} {S : WeakSystem (Fin n) (K + 1)}
variable {pins : Fin n → Option (Fin (K + 1))}

/-- A raw structural certificate, containing no probability or approximation
conclusion. Its rank need not agree with the original label indices. -/
structure SparseBounds (P : SourcePartition S pins) (H d : ℕ) where
  rank : Fin n → ℕ
  strict : ∀ x y, Arc P.active x y → rank x < rank y
  height : ∀ x, rank x + 1 ≤ H
  degree : ∀ x, (neighbors P.active x).card ≤ d

/-- Count an already stored numerical view on its sufficient ball union. -/
def branchOnBall (V : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x y : Fin n) : ℚ :=
  branchEstimate (induced V (LocalAccuracy.queryBall V H d R ε x y))
    ⟨x, LocalAccuracy.left_mem_queryBall V H d R ε x y⟩
    ⟨y, LocalAccuracy.right_mem_queryBall V H d R ε x y⟩

def cdfOnBall (V : WeakSystem (Fin n) (K + 1)) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) : ℚ :=
  cdfEstimate (induced V (CDFAccuracy.queryBall V H d R ε x))
    ⟨x, CDFAccuracy.mark_mem_queryBall V H d R ε x⟩ cut

/-- The comparison routine stores the current sparse rows and globally
propagated lists once, then invokes the local dynamic program. -/
def qBranch (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x y : Fin n) : ℚ :=
  let V := Materialize.system P.view
  branchOnBall V H d R ε x y

/-- CDF evaluations for one mark share one fixed ball for all thresholds. -/
def qCDF (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) : ℚ :=
  let V := Materialize.system P.view
  cdfOnBall V H d R ε x cut

theorem qBranch_eq_reference (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hne : ∃ f, S.Valid f) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    qBranch P H d R ε x y = LocalAccuracy.localWeakProbability P.view H d R ε x y := by
  change branchOnBall (Materialize.system P.view) H d R ε x y = _
  rw [Materialize.system_eq]
  simp only [branchOnBall, branchEstimate_eq,
    LocalAccuracy.localWeakProbability, P.propagate_view hp hne]

theorem qCDF_eq_reference (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hne : ∃ f, S.Valid f) (H d : ℕ) (R ε : ℚ) (x : Fin n) (cut : ℕ) :
    qCDF P H d R ε x cut = CDFAccuracy.localCDF P.view H d R ε x cut := by
  change cdfOnBall (Materialize.system P.view) H d R ε x cut = _
  rw [Materialize.system_eq]
  simp only [cdfOnBall, cdfEstimate_eq,
    CDFAccuracy.localCDF, P.propagate_view hp hne]

/-- Actual DP comparison accuracy against the full parent law, including
isolated marks of arbitrary width. -/
theorem qBranch_accuracy (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x y : Fin n) (hxy : y ≠ x)
    (hx : MarkCondition P.view H d R ε x) (hy : MarkCondition P.view H d R ε y) :
    |qBranch P H d R ε x y - weakProbability S x y| ≤ ε := by
  have hv : 0 < P.view.count := by rw [P.view_count hp]; exact hS
  rw [qBranch_eq_reference P hp (S.count_pos_iff.mp hS)]
  have heq := weakProbability_congr (P.view_valid hp) x y
  rw [← heq]
  exact Reindexing.comparison_accuracy P.view hv g.rank H d g.strict g.height g.degree
    R ε hR hε x y hxy hx hy

/-- Actual DP CDF accuracy for every natural threshold against the original
parent pool, rather than merely the sparse numerical representation. -/
theorem qCDF_accuracy (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x : Fin n)
    (hx : MarkCondition P.view H d R ε x) (cut : ℕ) :
    |qCDF P H d R ε x cut - MarginalCalibration.cdf S x cut| ≤ ε := by
  have hv : 0 < P.view.count := by rw [P.view_count hp]; exact hS
  rw [qCDF_eq_reference P hp (S.count_pos_iff.mp hS)]
  have heq := CDFCoupling.cdf_congr (P.view_valid hp) x cut
  rw [← heq]
  exact Reindexing.cdf_accuracy P.view hv g.rank H d g.strict g.height g.degree
    R ε hR hε x hx cut

/-- Propagated numerical widths are exactly the natural effective widths
tested by the normalization controller. -/
theorem view_width (P : SourcePartition S pins) (hne : ∃ f, S.Valid f) (x : Fin n) :
    windowWidth P.view x = (CutNormalization.width S x : ℚ) := by
  have hle : (S.effectiveLower x).val ≤ (S.effectiveUpper x).val :=
    (S.feasible_iff_windows P.closed).mp hne x
  unfold windowWidth SourcePartition.view CutNormalization.width
  rw [Nat.cast_sub (by omega : (S.effectiveLower x).val ≤ (S.effectiveUpper x).val + 1),
    Nat.cast_add, Nat.cast_one]
  ring

/-- A direct bridge from actual normalization tests to the local theorem's
mark premise. Isolated labels require no width condition. -/
theorem markCondition_of_widths (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hne : ∃ f, S.Valid f) (H d : ℕ) (R ε : ℚ) (x : Fin n)
    (hx : IsolatedCoupling.Isolated P.active x ∨
      ((∀ v, Connected P.active x v →
        (CutNormalization.width S v : ℚ) ≤ R * CutNormalization.width S x) ∧
        (LocalParameters.minimumWidth H (LocalAccuracy.influenceSize H d) R ε : ℚ) ≤
          CutNormalization.width S x)) : MarkCondition P.view H d R ε x := by
  unfold MarkCondition
  rw [P.propagate_view hp hne]
  simp only [view_width P hne]
  exact hx

/-- The stopping comparison's numerical choice uses the computed estimates. -/
def chooseBranch (P : SourcePartition S pins) (H d : ℕ) (R ε : ℚ) (x y : Fin n) :
    WeakSystem (Fin n) (K + 1) :=
  chooseFromEstimates S x y (qBranch P H d R ε x y) (qBranch P H d R ε y x)

theorem chooseBranch_retains (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (x y : Fin n) (hxy : y ≠ x)
    (hx : MarkCondition P.view H d R ε x) (hy : MarkCondition P.view H d R ε y) :
    (1 / 2 : ℚ) - ε ≤ ((chooseBranch P H d R ε x y).count : ℚ) / S.count :=
  approximate_larger_branch S x y hS _ _ ε
    (qBranch_accuracy P hp hS H d g R ε hR hε x y hxy hx hy)
    (qBranch_accuracy P hp hS H d g R ε hR hε y x hxy.symm hy hx)

theorem chooseBranch_count_pos (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R ε : ℚ) (hR : 0 ≤ R) (hε : 0 < ε) (hsmall : ε < 1 / 2)
    (x y : Fin n) (hxy : y ≠ x)
    (hx : MarkCondition P.view H d R ε x) (hy : MarkCondition P.view H d R ε y) :
    0 < (chooseBranch P H d R ε x y).count :=
  approximate_choice_count_pos S x y hS _ _ ε hsmall
    (qBranch_accuracy P hp hS H d g R ε hR hε x y hxy hx hy)
    (qBranch_accuracy P hp hS H d g R ε hR hε y x hxy.symm hy hx)

/-- A checked `1/16` CDF evaluator for ordinary structural promotions. -/
theorem qCDF_sixteenth (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R : ℚ) (hR : 0 ≤ R) (x : Fin n)
    (hx : MarkCondition P.view H d R (1 / 16) x) (i : Fin (K + 1)) :
    |qCDF P H d R (1 / 16) x (i.val + 1) - MarginalCalibration.cdf S x (i.val + 1)| ≤
      (1 / 16 : ℚ) :=
  qCDF_accuracy P hp hS H d g R (1 / 16) hR (by norm_num) x hx (i.val + 1)

/-- Executable finite quartile search fed by the actual local dynamic program.
All graph and accuracy arguments are proofs and vanish from evaluation. -/
def calibrationInterval (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R : ℚ) (hR : 0 ≤ R) (x : Fin n)
    (hx : MarkCondition P.view H d R (1 / 16) x) : Fin (K + 1) × Fin (K + 1) :=
  MarginalCalibration.selectedInterval S x hS
    (fun i => qCDF P H d R (1 / 16) x (i.val + 1))
    (qCDF_sixteenth P hp hS H d g R hR x hx)

/-- Every color in the computed interval has the true parent's calibrated
mass. This theorem has no noisy-CDF hypothesis left to discharge. -/
theorem calibration_mass (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R : ℚ) (hR : 0 ≤ R) (x : Fin n)
    (hx : MarkCondition P.view H d R (1 / 16) x) :
    let I := calibrationInterval P hp hS H d g R hR x hx
    I.1 ≤ I.2 ∧ ∀ i : ℕ, I.1.val ≤ i → i ≤ I.2.val →
      1 / (16 * (I.2.val + 1 - I.1.val : ℕ) : ℚ) ≤ mass S x i :=
  noisy_quartile_calibration S x hS _ (qCDF_sixteenth P hp hS H d g R hR x hx)

/-- Denominator-free retention certificate for any actual selected color in
the interval returned by the executable local oracle. -/
theorem calibration_fiber_count (P : SourcePartition S pins) (hp : FiniteRefinement.PinBounds S pins)
    (hS : 0 < S.count) (H d : ℕ) (g : SparseBounds P H d)
    (R : ℚ) (hR : 0 ≤ R) (x : Fin n)
    (hx : MarkCondition P.view H d R (1 / 16) x) (c : Fin (K + 1))
    (hl : (calibrationInterval P hp hS H d g R hR x hx).1 ≤ c)
    (hu : c ≤ (calibrationInterval P hp hS H d g R hR x hx).2) :
    S.count ≤ 16 * ((calibrationInterval P hp hS H d g R hR x hx).2.val + 1 -
      (calibrationInterval P hp hS H d g R hR x hx).1.val) * (S.fiber x c).card :=
  selected_parent_fiber_count S x hS _ (qCDF_sixteenth P hp hS H d g R hR x hx) c hl hu

end SortingAdversary.Optimal.LocalOracle
