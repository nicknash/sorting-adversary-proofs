import SortingAdversary.StrengthenedCurvature.ScalarEnvelope

/-!
# Exact rational displacement schedule

Table 1 of the strengthened-curvature source.  Every decimal is represented
by the exact integer numerator stated in the paper; interpolation occurs only
after coercion to the reals.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

private def deltaNumerators : List ℕ :=
  [0, 20, 40, 60, 80, 100, 120, 140, 160, 180, 200, 220,
    240, 260, 280, 300, 320, 340, 360, 380, 400, 410, 411]

private def aNumerators : List ℕ :=
  [622454434, 619095674, 615380539, 611228294, 606581110,
    601325567, 595325316, 588378953, 580204170, 570394627,
    558360320, 543240708, 523955919, 503631525, 484458268,
    465515284, 446808252, 428343050, 410125825, 392162933,
    374460973, 365700000, 364823903]

private def bNumerators : List ℕ :=
  [622424669, 625535911, 628496630, 631313547, 633952170,
    636408839, 638653695, 640666245, 642417260, 643880998,
    645041599, 645950414, 647234041, 627425532, 576626027,
    602315113, 631351002, 660180668, 707228286, 690669770,
    732158061, 750000000, 751784194]

/-- A delta knot, with denominator `1000`. -/
def scheduleDelta (i : Fin 23) : ℚ :=
  deltaNumerators.get i / 1000

/-- A positive displacement knot, with denominator `10^9`. -/
def scheduleAKnot (i : Fin 23) : ℚ :=
  aNumerators.get i / 1000000000

/-- A negative displacement knot, with denominator `10^9`. -/
def scheduleBKnot (i : Fin 23) : ℚ :=
  bNumerators.get i / 1000000000

/-- Linear interpolation weight in one schedule segment. -/
noncomputable def scheduleWeight (i : Fin 22) (delta : ℝ) : ℝ :=
  let left : Fin 23 := i.castSucc
  let right : Fin 23 := i.succ
  (delta - scheduleDelta left) / (scheduleDelta right - scheduleDelta left)

/-- Interpolated positive trial displacement. -/
noncomputable def scheduleA (i : Fin 22) (delta : ℝ) : ℝ :=
  let left : Fin 23 := i.castSucc
  let right : Fin 23 := i.succ
  scheduleAKnot left + scheduleWeight i delta *
    (scheduleAKnot right - scheduleAKnot left)

/-- Interpolated negative trial displacement. -/
noncomputable def scheduleB (i : Fin 22) (delta : ℝ) : ℝ :=
  let left : Fin 23 := i.castSucc
  let right : Fin 23 := i.succ
  scheduleBKnot left + scheduleWeight i delta *
    (scheduleBKnot right - scheduleBKnot left)

/-- A delta belongs to the closed segment indexed by `i`. -/
def InScheduleSegment (i : Fin 22) (delta : ℝ) : Prop :=
  scheduleDelta i.castSucc ≤ delta ∧ delta ≤ scheduleDelta i.succ

end StrengthenedCurvature
end SortingAdversary
