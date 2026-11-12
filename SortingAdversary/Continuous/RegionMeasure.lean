import SortingAdversary.Continuous.OrderRegion
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The uniform probability measure on an actual order region

This is normalized restricted Lebesgue measure, not a supplied probability
oracle.  The normalization is valid whenever the finite order region is
nonempty.  Its event probabilities are the volume ratios used by `Select`.
-/

namespace SortingAdversary.Continuous.OrderRegion

open FiniteAveraging MeasureTheory Set
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def uniformMeasure (D : System ι ℝ) : Measure (ι → ℝ) :=
  (volume (region D))⁻¹ • volume.restrict (region D)

theorem uniformMeasure_apply (D : System ι ℝ) (E : Set (ι → ℝ))
    (hE : MeasurableSet E) :
    uniformMeasure D E = volume (E ∩ region D) / volume (region D) := by
  rw [uniformMeasure, Measure.smul_apply, Measure.restrict_apply hE]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem isProbabilityMeasure_uniformMeasure (D : System ι ℝ)
    (hV : 0 < volume (region D)) : IsProbabilityMeasure (uniformMeasure D) := by
  constructor
  rw [uniformMeasure_apply D univ MeasurableSet.univ, univ_inter]
  exact ENNReal.div_self (ne_of_gt hV) (volume_ne_top D)

theorem uniformMeasure_region (D : System ι ℝ)
    (hV : 0 < volume (region D)) : uniformMeasure D (region D) = 1 := by
  rw [uniformMeasure_apply D (region D) (region_open D).measurableSet, inter_self]
  exact ENNReal.div_self (ne_of_gt hV) (volume_ne_top D)

theorem uniformMeasure_ae_feasible (D : System ι ℝ) :
    ∀ᵐ X ∂uniformMeasure D, D.StrictlyFeasible X := by
  rw [ae_iff]
  change uniformMeasure D (region D)ᶜ = 0
  rw [uniformMeasure_apply D (region D)ᶜ (region_open D).measurableSet.compl]
  simp

/-- The exact event/volume identity used when recording an answer. -/
theorem uniformMeasure_real (D : System ι ℝ) (E : Set (ι → ℝ))
    (hE : MeasurableSet E) :
    (uniformMeasure D).real E = (volume (E ∩ region D)).toReal / nodeVolume D := by
  rw [Measure.real_def, uniformMeasure_apply D E hE, ENNReal.toReal_div]
  rfl

theorem volume_ratio_of_event (D D' : System ι ℝ) (E : Set (ι → ℝ))
    (hE : MeasurableSet E) (hregion : region D' = E ∩ region D) :
    (uniformMeasure D).real E = nodeVolume D' / nodeVolume D := by
  rw [uniformMeasure_real D E hE, ← hregion]
  rfl

theorem retained_volume (D D' : System ι ℝ) (E : Set (ι → ℝ)) (r : ℝ)
    (hE : MeasurableSet E) (hregion : region D' = E ∩ region D)
    (hV : 0 < nodeVolume D) (hprob : r ≤ (uniformMeasure D).real E) :
    r * nodeVolume D ≤ nodeVolume D' := by
  rw [volume_ratio_of_event D D' E hE hregion] at hprob
  exact (le_div_iff₀ hV).mp hprob

end SortingAdversary.Continuous.OrderRegion
