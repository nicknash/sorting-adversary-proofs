import SortingAdversary.Optimal.StructuralNormalize
import SortingAdversary.Optimal.LocalOracleWork
import SortingAdversary.Optimal.StageScalars
import SortingAdversary.Optimal.AsymptoticRates

/-!
# Concrete scalar stages for the executable adversary

Ordinary degree and path targets have separate maintenance bounds. The
integer width threshold pays for both actual oracle tolerances, and the
local-ball allowances use the exact sweep counts. These reference integers
are specifications; `UniformStage` evaluates their fixed recipe with caps.
-/

namespace SortingAdversary.Optimal.StageParameters

open WidthRepair LocalParameters

def degree (j : ℕ) : ℕ := j + 4
def pathLength (j : ℕ) : ℕ := 2 ^ j
def height (j : ℕ) : ℕ := 2 * pathLength j
def degreeCap (j : ℕ) : ℕ := degree j + 1
def comparables (j : ℕ) : ℕ := (degreeCap j + 1) ^ (height j + 1)
def insertion (j : ℕ) : ℕ := 2 * 4 ^ comparables j
def accuracyDen (j : ℕ) : ℕ := 100 * j
def edgeRatio (j : ℕ) : ℕ := (accuracyDen j * (degreeCap j + 1) + 1) * insertion j
def scaleLength (j : ℕ) : ℕ := 2 ^ (j * (comparables j + 2) ^ 2)
def scaleBase (j : ℕ) : ℕ := 128 * scaleLength j * (edgeRatio j + 1) ^ (2 * height j + 3)
def componentRatio (j : ℕ) : ℕ := scaleBase j ^ (scaleLength j + 1)
def localInsertion (j : ℕ) : ℕ := insertionConstant (comparables j)
def moment (j : ℕ) : ℕ := momentOrder (height j) (comparables j)
def comparisonSweeps (j : ℕ) : ℕ :=
  StageScalars.sweeps (height j) (comparables j) (componentRatio j) (accuracyDen j)
def cdfSweeps (j : ℕ) : ℕ := StageScalars.sweeps (height j) (comparables j) (componentRatio j) 16
def comparisonWidth (j : ℕ) : ℕ :=
  StageScalars.widthNeed (height j) (comparables j) (componentRatio j) (accuracyDen j)
def cdfWidth (j : ℕ) : ℕ := StageScalars.widthNeed (height j) (comparables j) (componentRatio j) 16
def minimumWidth (j : ℕ) : ℕ := max 32 (max (comparisonWidth j) (cdfWidth j))
def cheap (j : ℕ) : ℕ := minimumWidth j * 4 ^ comparables j
def comparisonBall (j : ℕ) : ℕ := 2 * (degreeCap j + 1) ^ (height j * comparisonSweeps j)
def cdfBall (j : ℕ) : ℕ := (degreeCap j + 1) ^ (height j * cdfSweeps j)

inductive Field where
  | degree | pathLength | height | degreeCap | comparables | insertion | accuracyDen
  | edgeRatio | scaleLength | scaleBase | componentRatio | localInsertion | moment
  | comparisonSweeps | cdfSweeps | comparisonWidth | cdfWidth | minimumWidth
  | cheap | cheapSquare | comparisonBall | cdfBall
  deriving DecidableEq, Repr

def fields : List Field := [ .degree, .pathLength, .height, .degreeCap, .comparables, .insertion,
  .accuracyDen, .edgeRatio, .scaleLength, .scaleBase, .componentRatio, .localInsertion, .moment,
  .comparisonSweeps, .cdfSweeps, .comparisonWidth, .cdfWidth, .minimumWidth, .cheap, .cheapSquare,
  .comparisonBall, .cdfBall ]

theorem mem_fields (f : Field) : f ∈ fields := by cases f <;> simp [fields]

def value (j : ℕ) : Field → ℕ
  | .degree => degree j
  | .pathLength => pathLength j
  | .height => height j
  | .degreeCap => degreeCap j
  | .comparables => comparables j
  | .insertion => insertion j
  | .accuracyDen => accuracyDen j
  | .edgeRatio => edgeRatio j
  | .scaleLength => scaleLength j
  | .scaleBase => scaleBase j
  | .componentRatio => componentRatio j
  | .localInsertion => localInsertion j
  | .moment => moment j
  | .comparisonSweeps => comparisonSweeps j
  | .cdfSweeps => cdfSweeps j
  | .comparisonWidth => comparisonWidth j
  | .cdfWidth => cdfWidth j
  | .minimumWidth => minimumWidth j
  | .cheap => cheap j
  | .cheapSquare => cheap j ^ 2
  | .comparisonBall => comparisonBall j
  | .cdfBall => cdfBall j

theorem accuracyDen_pos {j : ℕ} (hj : 0 < j) : 0 < accuracyDen j := by unfold accuracyDen; omega
theorem insertion_pos (j : ℕ) : 0 < insertion j := by unfold insertion; positivity

theorem cutBudget {j : ℕ} (hj : 0 < j) : 2 * 4 ^ comparables j < edgeRatio j := by
  have he := accuracyDen_pos hj
  have hc := insertion_pos j
  have hd : 0 < degreeCap j + 1 := Nat.succ_pos _
  change insertion j < (accuracyDen j * (degreeCap j + 1) + 1) * insertion j
  have hm := Nat.mul_pos he hd
  simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right
    (show 1 < accuracyDen j * (degreeCap j + 1) + 1 by omega) hc

theorem path_two {j : ℕ} (hj : 0 < j) : 2 ≤ pathLength j := by
  simpa only [pathLength, pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hj

theorem scale_four {j : ℕ} (hj : 0 < j) : 4 ≤ scaleLength j := by
  have he : 2 ≤ j * (comparables j + 2) ^ 2 := by nlinarith [Nat.zero_le (comparables j)]
  simpa only [scaleLength] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) he

theorem comparison_minimum {j : ℕ} (hj : 0 < j) :
    LocalParameters.minimumWidth (height j) (comparables j) (componentRatio j)
      (1 / (accuracyDen j : ℚ)) ≤ minimumWidth j := by
  rw [StageScalars.widthNeed_eq _ _ _ _ (accuracyDen_pos hj)]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem cdf_minimum (j : ℕ) :
    LocalParameters.minimumWidth (height j) (comparables j) (componentRatio j) (1 / 16) ≤ minimumWidth j := by
  rw [show (1 / 16 : ℚ) = 1 / ((16 : ℕ) : ℚ) by norm_num,
    StageScalars.widthNeed_eq _ _ _ _ (by decide)]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem comparison_ball (j : ℕ) (hj : 0 < j) :
    LocalOracleWork.comparisonBallBound (height j) (degreeCap j) (componentRatio j)
      (1 / (accuracyDen j : ℚ)) = comparisonBall j := by
  unfold LocalOracleWork.comparisonBallBound
  change 2 * (degreeCap j + 1) ^ (height j * LocalParameters.sweepCount (height j)
    (comparables j) (componentRatio j) (1 / (accuracyDen j : ℚ))) = _
  rw [StageScalars.sweeps_eq _ _ _ _ (accuracyDen_pos hj)]
  rfl

theorem cdf_ball (j : ℕ) :
    LocalOracleWork.cdfBallBound (height j) (degreeCap j) (componentRatio j) (1 / 16) = cdfBall j := by
  unfold LocalOracleWork.cdfBallBound
  change (degreeCap j + 1) ^ (height j * LocalParameters.sweepCount (height j)
    (comparables j) (componentRatio j) (1 / ((16 : ℕ) : ℚ))) = _
  rw [StageScalars.sweeps_eq _ _ _ _ (by decide)]
  rfl

/-- The package needed by the recursive query router and normalization
controller. Its fields are ordinary stored integers and a rational accuracy. -/
structure Runtime where
  normalizer : StructuralNormalize.Parameters
  ε : ℚ
  error_pos : 0 < ε
  error_small : ε < 1 / 2
  height_budget : 2 * normalizer.H ≤ normalizer.scale.H
  degree_budget : normalizer.D + 1 ≤ normalizer.d
  comparable_budget : (normalizer.d + 1) ^ (normalizer.scale.H + 1) ≤ normalizer.scale.width.B
  comparison_minimum : LocalParameters.minimumWidth normalizer.scale.H
    (LocalAccuracy.influenceSize normalizer.scale.H normalizer.d) normalizer.scale.R ε ≤ normalizer.scale.width.W₀
  cheap : ℕ
  cheap_eq : cheap = normalizer.scale.width.W₀ * 4 ^ normalizer.scale.width.B
  comparisonBall : ℕ
  comparisonBall_eq : comparisonBall = LocalOracleWork.comparisonBallBound normalizer.scale.H
    normalizer.d normalizer.scale.R ε
  cdfBall : ℕ
  cdfBall_eq : cdfBall = LocalOracleWork.cdfBallBound normalizer.scale.H normalizer.d normalizer.scale.R (1 / 16)

/-- Construction from already evaluated scalar fields. Equality witnesses
are proofs; every runtime field comes from `v`, never the enormous references. -/
def fromValues (j : ℕ) (hj : 0 < j) (v : Field → ℕ) (hv : ∀ f, v f = value j f) : Runtime where
  normalizer := {
    scale := {
      width := {
        W₀ := v .minimumWidth
        B := v .comparables
        L := v .edgeRatio
        large := by rw [hv .minimumWidth]; exact le_max_left _ _
        cutBudget := by rw [hv .comparables, hv .edgeRatio]; exact cutBudget hj }
      H := v .height
      J := v .scaleLength
      group := by rw [hv .scaleLength]; exact scale_four hj }
    d := v .degreeCap
    D := v .degree
    H := v .pathLength
    degree_pos := by rw [hv .degree]; change 0 < j + 4; omega
    path_two := by rw [hv .pathLength]; exact path_two hj
    minimum := by
      simp only [hv, value, ScaleParameters.R, ScaleParameters.A, ScaleGeometry.scaleBase,
        LocalAccuracy.influenceSize]
      exact cdf_minimum j }
  ε := 1 / (v .accuracyDen : ℚ)
  error_pos := by rw [hv .accuracyDen]; exact div_pos (by norm_num) (by exact_mod_cast accuracyDen_pos hj)
  error_small := by
    rw [hv .accuracyDen]
    have he : (2 : ℚ) < accuracyDen j := by unfold accuracyDen; exact_mod_cast (show 2 < 100 * j by omega)
    exact div_lt_div_of_pos_left (by norm_num) (by norm_num) he
  height_budget := by simp only [hv, value]; exact le_rfl
  degree_budget := by simp only [hv, value]; exact le_rfl
  comparable_budget := by simp only [hv, value]; exact le_rfl
  comparison_minimum := by
    simp only [hv, value, ScaleParameters.R, ScaleParameters.A, ScaleGeometry.scaleBase,
      LocalAccuracy.influenceSize]
    exact comparison_minimum hj
  cheap := v .cheap
  cheap_eq := by simp only [hv, value]; rfl
  comparisonBall := v .comparisonBall
  comparisonBall_eq := by
    simp only [hv, value, ScaleParameters.R, ScaleParameters.A, ScaleGeometry.scaleBase]
    exact (comparison_ball j hj).symm
  cdfBall := v .cdfBall
  cdfBall_eq := by
    simp only [hv, value, ScaleParameters.R, ScaleParameters.A, ScaleGeometry.scaleBase]
    exact (cdf_ball j).symm

theorem fromValues_degree (j : ℕ) (hj : 0 < j) (v : Field → ℕ) (hv : ∀ f, v f = value j f) :
    (fromValues j hj v hv).normalizer.D = AsymptoticRates.stageDegree j := hv .degree

theorem fromValues_path (j : ℕ) (hj : 0 < j) (v : Field → ℕ) (hv : ∀ f, v f = value j f) :
    (fromValues j hj v hv).normalizer.H = AsymptoticRates.stagePathLength j := hv .pathLength

theorem fromValues_scale (j : ℕ) (hj : 0 < j) (v : Field → ℕ) (hv : ∀ f, v f = value j f) :
    (fromValues j hj v hv).normalizer.scale.J =
      AsymptoticRates.stageScaleLength j (fromValues j hj v hv).normalizer.scale.width.B := by
  change v .scaleLength = AsymptoticRates.stageScaleLength j (v .comparables)
  rw [hv .scaleLength, hv .comparables]
  rfl

end SortingAdversary.Optimal.StageParameters
