import SortingAdversary.Optimal.WidthPolynomialWork
import SortingAdversary.Optimal.UniformScalarSizes
import SortingAdversary.Optimal.MeasuredStructuralWork
import SortingAdversary.Optimal.MeasuredOracleBudget

/-!
# A concrete counted repair for every accepted uniform stage

The ordinary executor uses the counted local subset DP, at a radius computed
once by `prepare`. The width executor performs its actual cheap pins, cuts,
shortest-path reservations, and chronological hub promotions. The structural
loop is the measured degree/path implementation. No executor or accuracy
callback is an argument of the resulting repair.

The common size bound includes palette growth during a repair. Its decrease
along each actual primitive step supplies every recursive call's palette
bound. The logarithmic ball convention is exactly `log₂(n+1)`: the subset-DP
work bound uses budget `2*n`, including the boundary sizes `n = 2^k-1`.
-/

namespace SortingAdversary.Optimal.UniformRepairWork

open PrimitiveWork WidthRepair RepresentationWork LocalOracle MeasuredRepairBounds
open UniformStage

variable {n j : ℕ}

/-- Runtime stage data needed repeatedly by the counted ordinary pins. -/
structure Prepared (a : Accepted (Parameters.logCap n) j) where
  radius : ℕ
  exact : radius = a.runtime.normalizer.scale.H *
    LocalParameters.sweepCount a.runtime.normalizer.scale.H
      (LocalAccuracy.influenceSize a.runtime.normalizer.scale.H a.runtime.normalizer.d)
      a.runtime.normalizer.scale.R (1 / 16)

/-- Actual arithmetic for the cached CDF radius; only its certificate erases. -/
def prepare (a : Accepted (Parameters.logCap n) j) : Result (Prepared a) :=
  let radius := UniformScalarWork.cdf a
  ⟨⟨radius.value, UniformScalarWork.cdf_value a⟩, radius.work + 1⟩

theorem prepare_work (a : Accepted (Parameters.logCap n) j) :
    (prepare a).work ≤ 14 * Parameters.logCap n + 40 := by
  have h := UniformScalarWork.cdf_work a
  change (UniformScalarWork.cdf a).work + 1 ≤ _
  omega

theorem prepare_radius (a : Accepted (Parameters.logCap n) j) :
    (prepare a).value.radius ≤ Parameters.logCap n := UniformScalarWork.cdf_cap a

/-- The concrete ordinary executor closes over a previously paid-for radius. -/
def ordinary (a : Accepted (Parameters.logCap n) j) (data : Prepared a) :
    MeasuredOrdinaryPromotion.Executor n a.runtime.normalizer.scale.H
      a.runtime.normalizer.d a.runtime.normalizer.scale.R :=
  MeasuredOrdinaryPromotion.executor _ _ _ data.radius data.exact

def ordinaryBound (n cap : ℕ) : ℕ :=
  MeasuredOrdinaryPromotion.workBound n cap 2
    (MeasuredOracleBudget.cdfPolynomial n (2 * n) (cap + 1) 2) + 1

theorem ordinary_workBound_mono {n palette palette' A C : ℕ} (hp : palette ≤ palette') :
    MeasuredOrdinaryPromotion.workBound n palette A C ≤
      MeasuredOrdinaryPromotion.workBound n palette' A C := by
  unfold MeasuredOrdinaryPromotion.workBound MeasuredOrdinaryPromotion.chooseBound
    CalibrationWork.firstBound HubWork.windowPolynomial MeasuredPin.workBound
    LocalAccess.cacheBound
  gcongr

theorem ordinary_bound (a : Accepted (Parameters.logCap n) j) (data : Prepared a) (cap : ℕ) :
    OrdinaryBound a.runtime.normalizer (ordinary a data) cap (ordinaryBound n cap) := by
  intro s access cached g v hmark hv hm hsize
  have hn : n ≠ 0 := Nat.ne_of_gt (UniformScalarWork.input_pos a)
  have hp : s.pool.palette ≤ cap := (Nat.le_add_right _ _).trans hsize
  have hpalette : s.pool.palette + 1 ≤ (cap + 1) * n :=
    (Nat.add_le_add_right hp 1).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hball : (GraphBalls.ball s.rows.active v data.radius).card ≤ Parameters.logCap n := by
    rw [data.exact]
    exact (CDFAccuracy.queryBall_card s.rows.view _ _ _ _ g.degree v).trans a.cdfBall_cap
  have h := MeasuredOracleBudget.ordinary_work_logCap access cached _ _ g _ (by positivity)
    v hmark hv hm data.radius data.exact (cap + 1) hn hball hpalette
  exact h.trans (Nat.add_le_add_right (ordinary_workBound_mono hp) 1)

/-- A reference-free assembly of the three concrete counted repair loops. -/
def atRadius (a : Accepted (Parameters.logCap n) j) (data : Prepared a)
    (s : State n) (g : SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank) :
    Result (MeasuredStructuralNormalize.Output s a.runtime.normalizer g hB) :=
  MeasuredStructuralNormalize.normalize MeasuredWidthNormalize.executor a.runtime.normalizer
    (ordinary a data) s g hB access cached rank rank_eq

theorem atRadius_actual (a : Accepted (Parameters.logCap n) j) (data : Prepared a)
    (s : State n) (g : SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank) :
    (atRadius a data s g hB access cached rank rank_eq).value.result =
      StructuralNormalize.normalize s a.runtime.normalizer g hB :=
  (atRadius a data s g hB access cached rank rank_eq).value.actual

/-- An explicit polynomial in `n` and the initial palette-plus-potential cap. -/
def repairBound (n cap : ℕ) : ℕ :=
  (n + n * n + 1) * MeasuredStructuralNormalize.kernelBound n (n + 1) 2
    (WidthPolynomialWork.bound n cap (n + 1)) (ordinaryBound n cap)

theorem atRadius_work_le (a : Accepted (Parameters.logCap n) j) (data : Prepared a)
    (s : State n) (g : SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank)
    (hrank : ∀ v, (rank v).work ≤ 2) (cap : ℕ) (hcap : size s ≤ cap) :
    (atRadius a data s g hB access cached rank rank_eq).work ≤ repairBound n cap := by
  have hlog : Parameters.logCap n ≤ n + 1 := Nat.log_le_self 2 (n + 1)
  have hh : a.runtime.normalizer.scale.H ≤ n + 1 := a.height_cap.trans hlog
  have hw : WidthBound (MeasuredWidthNormalize.executor (n := n))
      a.runtime.normalizer.scale a.runtime.normalizer.d cap (WidthPolynomialWork.bound n cap (n + 1)) := by
    intro t getters hget graph comparable hsize
    exact (WidthPolynomialWork.admitted_bound a n cap getters hget graph comparable hsize).trans
      (WidthPolynomialWork.bound_mono hlog)
  have h := MeasuredStructuralNormalize.normalize_work_le MeasuredWidthNormalize.executor
    a.runtime.normalizer (ordinary a data) cap (WidthPolynomialWork.bound n cap (n + 1))
    (ordinaryBound n cap) 2 hw (ordinary_bound a data cap) s g hB access cached rank rank_eq hrank hcap
  apply h.trans
  unfold repairBound MeasuredStructuralNormalize.kernelBound LongestPathWork.chainBound LongestPathWork.tableBound
  have hm := measure_le s
  gcongr

/-- This cap covers a pre-repair palette bounded by `2*n+1`, including
all later endpoint births paid for by the decreasing repair potential. -/
def localCap (n : ℕ) : ℕ := 3 * n + n * n + 1

theorem size_le_localCap {s : State n} (hpalette : s.pool.palette ≤ 2 * n + 1) :
    size s ≤ localCap n := by
  have h := measure_le s
  unfold size localCap
  omega

/-- A single fixed arithmetic polynomial, independent of the accepted stage. -/
def polynomial (n : ℕ) : ℕ := 14 * (n + 1) + 41 + repairBound n (localCap n)

/-- The standalone repair also includes the cost of constructing its radius.
An online implementation can instead call `prepare` once and reuse `atRadius`. -/
def normalize (a : Accepted (Parameters.logCap n) j)
    (s : State n) (g : SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank) :
    Result (MeasuredStructuralNormalize.Output s a.runtime.normalizer g hB) :=
  let initialized := prepare a
  let repaired := atRadius a initialized.value s g hB access cached rank rank_eq
  ⟨repaired.value, initialized.work + repaired.work + 1⟩

theorem normalize_actual (a : Accepted (Parameters.logCap n) j)
    (s : State n) (g : SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank) :
    (normalize a s g hB access cached rank rank_eq).value.result =
      StructuralNormalize.normalize s a.runtime.normalizer g hB :=
  (normalize a s g hB access cached rank rank_eq).value.actual

theorem normalize_work_le (a : Accepted (Parameters.logCap n) j)
    (s : State n) (g : SparseBounds s.rows a.runtime.normalizer.scale.H a.runtime.normalizer.d)
    (hB : ComparableBound s a.runtime.normalizer.scale.width.B)
    (access : LocalAccess s) (cached : AccessBound access 2)
    (rank : LongestPathWork.Rank n) (rank_eq : LongestPathWork.rankValues rank = g.rank)
    (hrank : ∀ v, (rank v).work ≤ 2) (hpalette : s.pool.palette ≤ 2 * n + 1) :
    (normalize a s g hB access cached rank rank_eq).work ≤ polynomial n := by
  have hi := prepare_work a
  have hr := atRadius_work_le a (prepare a).value s g hB access cached rank rank_eq hrank
    (localCap n) (size_le_localCap hpalette)
  have hl : Parameters.logCap n ≤ n + 1 := Nat.log_le_self 2 (n + 1)
  change (prepare a).work + (atRadius a (prepare a).value s g hB access cached rank rank_eq).work + 1 ≤ _
  unfold polynomial
  omega

end SortingAdversary.Optimal.UniformRepairWork
