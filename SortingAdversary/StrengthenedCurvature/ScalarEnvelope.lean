import SortingAdversary.StrengthenedCurvature.EnergySplit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The two-variable scalar envelope

These are equations (41)--(57) of the strengthened-curvature source.  They are
kept as transparent definitions so that the finite certificate checks the
same expression that occurs in the analytic reduction.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

open intervalIntegral

/-- Positive-branch endpoint contribution, equation (46). -/
noncomputable def phiPlus (delta a x : ℝ) : ℝ :=
  let t := delta + a
  (2 * a / (1 + t ^ 2)) * x ^ 3 + 3 * (a * x - Real.log (1 + a * x))

/-- Negative-branch endpoint contribution, equation (48). -/
noncomputable def phiMinus (delta b x : ℝ) : ℝ :=
  let t := b - delta
  (-2 * b / (1 + t ^ 2)) * x ^ 3 + 3 * (-b * x - Real.log (1 - b * x))

/-- Convex combination of the two endpoint contributions. -/
noncomputable def phiAverage (delta a b lambda x : ℝ) : ℝ :=
  lambda * phiPlus delta a x + (1 - lambda) * phiMinus delta b x

/-- The continuously extended quotient from equation (51). -/
noncomputable def rho (delta a b lambda x : ℝ) : ℝ :=
  if x = 0 then (3 / 2 : ℝ) * (lambda * a ^ 2 + (1 - lambda) * b ^ 2)
  else phiAverage delta a b lambda x / x ^ 2

/-- Cross-over integrand on the sign class with energies `P²` and `N²`. -/
noncomputable def crossIntegrand (a P N s : ℝ) : ℝ :=
  (a - s) * (P / (1 + s * P) - N / (1 - s * N)) ^ 2

/-- Positive-displacement curvature saving from equation (41). -/
noncomputable def gammaPlus (a r : ℝ) : ℝ :=
  let P := Real.sqrt r
  let N := Real.sqrt (1 - r)
  if N ≥ P then a ^ 2 / 4 * (N - P) ^ 2
  else if N = 0 then
    (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..a, crossIntegrand a P N s
  else
    let s0 := (P - N) / (2 * P * N)
    (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..min a s0, crossIntegrand a P N s

/-- Negative-displacement saving obtained by reflection. -/
noncomputable def gammaMinus (b r : ℝ) : ℝ :=
  gammaPlus b (1 - r)

/-- Positive sign-class endpoint maximum, equation (55). -/
noncomputable def positiveEndpointMax (delta r a b lambda : ℝ) : ℝ :=
  max (rho delta a b lambda 0) (rho delta a b lambda (Real.sqrt r))

/-- Negative sign-class endpoint maximum, equation (56). -/
noncomputable def negativeEndpointMax (delta r a b lambda : ℝ) : ℝ :=
  max (rho delta a b lambda 0)
    (rho delta a b lambda (-Real.sqrt (1 - r)))

/-- The final scalar envelope `B`, equation (57). -/
noncomputable def scalarEnvelope (delta r a b lambda : ℝ) : ℝ :=
  lambda * Real.log (1 + 1 / (delta + a) ^ 2) +
    (1 - lambda) * Real.log (1 + 1 / (b - delta) ^ 2) +
    r * positiveEndpointMax delta r a b lambda +
    (1 - r) * negativeEndpointMax delta r a b lambda -
    lambda * gammaPlus a r - (1 - lambda) * gammaMinus b r

theorem min_le_weighted_average {x y lambda : ℝ}
    (hlower : 0 ≤ lambda) (hupper : lambda ≤ 1) :
    min x y ≤ lambda * x + (1 - lambda) * y := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy]
    nlinarith
  · rw [min_eq_right hyx]
    nlinarith

end StrengthenedCurvature
end SortingAdversary
