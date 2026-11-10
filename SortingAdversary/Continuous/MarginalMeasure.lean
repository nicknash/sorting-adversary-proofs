import SortingAdversary.Continuous.ProjectionDensity
import SortingAdversary.Continuous.RegionMeasure

/-!
# Actual marginal probabilities

The section-volume density is the marginal of normalized restricted Lebesgue
measure on the feasible region. This identity applies to every Borel event
in one coordinate, including unbounded tails and singletons.
-/

namespace SortingAdversary.Continuous.OrderRegion

open FiniteAveraging Density Set MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem density_integrable (D : System ι ℝ) (x : ι) : Integrable (density D x) :=
  (sectionVolume_integrable D x).div_const _

theorem density_nonneg (D : System ι ℝ) (x : ι) (t : ℝ) : 0 ≤ density D x t :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem coordinate_probability_eq_integral (D : System ι ℝ) (x : ι)
    (I : Set ℝ) (hI : MeasurableSet I) :
    (uniformMeasure D).real {X | X x ∈ I} = ∫ t in I, density D x t := by
  have hE : MeasurableSet {X : ι → ℝ | X x ∈ I} :=
    hI.preimage (measurable_pi_apply x)
  rw [uniformMeasure_real D _ hE]
  simp only [density, integral_div]
  congr 1
  have hb := ProjectionDensity.band_volume (region_open D).measurableSet
    (region_subset_box D) x I hI
  have hs (t : ℝ) : ProjectionDensity.slice (region D) x t = sectionAt D x t := by
    ext Y
    rfl
  simp only [ProjectionDensity.sectionVolume, hs] at hb
  simpa only [inter_comm, sectionVolume] using hb

theorem coordinate_singleton_probability (D : System ι ℝ) (x : ι) (t : ℝ) :
    (uniformMeasure D).real {X | X x = t} = 0 := by
  have h := coordinate_probability_eq_integral D x {t} (measurableSet_singleton t)
  simpa using h

end SortingAdversary.Continuous.OrderRegion
