import SortingAdversary.Continuous.Density
import SortingAdversary.Continuous.LocalEnclosure
import SortingAdversary.Continuous.RegionMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Stationarity on continuous order regions

The finite affine update acts on the actual conditional interval of the
updated coordinate. This file identifies that interval and lifts its scalar
tiling identity through Fubini to the full order region.
-/

namespace SortingAdversary.Continuous.Stationarity

open FiniteAveraging OrderRegion Density Set MeasureTheory
open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Constraints not involving the erased coordinate. -/
def eraseAt (D : System ι ℝ) (x : ι) : System (Remaining x) ℝ where
  lower y := D.lower y
  upper y := D.upper y
  edge y z := D.edge y z

theorem conditionalLower_restore (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (Y : Remaining x → ℝ) (c d : ℝ) :
    conditionalLower D x (restore x c Y) = conditionalLower D x (restore x d Y) := by
  apply Finset.fold_congr
  intro y hy
  have he : D.edge y x = true := by simpa using hy
  have hyx : y ≠ x := by rintro rfl; simp [hxx] at he
  simp [restore, hyx]

theorem conditionalUpper_restore (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (Y : Remaining x → ℝ) (c d : ℝ) :
    conditionalUpper D x (restore x c Y) = conditionalUpper D x (restore x d Y) := by
  apply Finset.fold_congr
  intro y hy
  have he : D.edge x y = true := by simpa using hy
  have hyx : y ≠ x := by rintro rfl; simp [hxx] at he
  simp [restore, hyx]

/-- Conditional endpoints are functions of the other coordinates alone. -/
def fiberLower (D : System ι ℝ) (x : ι) (Y : Remaining x → ℝ) : ℝ :=
  conditionalLower D x (restore x 0 Y)

def fiberUpper (D : System ι ℝ) (x : ι) (Y : Remaining x → ℝ) : ℝ :=
  conditionalUpper D x (restore x 0 Y)

/-- The full geometric fiber is exactly the interval used by `update`,
provided all constraints away from the updated coordinate hold. -/
theorem restore_feasible_iff (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (Y : Remaining x → ℝ) (c : ℝ) :
    D.StrictlyFeasible (restore x c Y) ↔
      (eraseAt D x).StrictlyFeasible Y ∧
        fiberLower D x Y < c ∧ c < fiberUpper D x Y := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro y
      simpa [eraseAt] using h.1 y
    · intro y z hyz
      simpa using h.2 y z hyz
    · have hc := conditional_mem_strict D x h
      rw [conditionalLower_restore D x hxx Y c 0,
        conditionalUpper_restore D x hxx Y c 0, restore_self] at hc
      exact hc
  · rintro ⟨hY, hlo, hhi⟩
    have hl := lower_le_conditionalLower D x (restore x 0 Y)
    have hu := conditionalUpper_le_upper D x (restore x 0 Y)
    constructor
    · intro y
      by_cases hy : y = x
      · subst y
        simpa using And.intro (hl.trans_lt hlo) (hhi.trans_le hu)
      · simpa [restore, hy, eraseAt] using hY.1 ⟨y, hy⟩
    · intro y z hyz
      by_cases hy : y = x
      · subst y
        have hz : z ≠ x := by rintro rfl; simp [hxx] at hyz
        have hzbound := conditionalUpper_le_successor D x z (restore x 0 Y) hyz
        simpa [restore, hz, fiberUpper] using hhi.trans_le hzbound
      · by_cases hz : z = x
        · subst z
          have hybound := predecessor_le_conditionalLower D x y (restore x 0 Y) hyz
          simpa [restore, hy, fiberLower] using hybound.trans_lt hlo
        · simpa [restore, hy, hz] using hY.2 ⟨y, hy⟩ ⟨z, hz⟩ hyz

theorem update_restore (D : System ι ℝ) (x : ι) (hxx : D.edge x x = false)
    (S : ℕ) (j : Fin S) (Y : Remaining x → ℝ) (c : ℝ) :
    update D S j x (restore x c Y) =
      restore x (digit S j c (fiberLower D x Y) (fiberUpper D x Y)) Y := by
  funext y
  by_cases hy : y = x
  · subst y
    simp only [update_self, restore_self]
    rw [conditionalLower_restore D x hxx Y c 0,
      conditionalUpper_restore D x hxx Y c 0]
    rfl
  · simp [update_other, hy, restore]

private theorem continuous_fold_max (s : Finset ι) (c : ℝ) :
    Continuous (fun Y : ι → ℝ => s.fold max c Y) := by
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : ι → ℝ => c))
  | @insert y s hy ih =>
    simp only [Finset.fold_insert hy]
    exact (continuous_apply y).max ih

private theorem continuous_fold_min (s : Finset ι) (c : ℝ) :
    Continuous (fun Y : ι → ℝ => s.fold min c Y) := by
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : ι → ℝ => c))
  | @insert y s hy ih =>
    simp only [Finset.fold_insert hy]
    exact (continuous_apply y).min ih

theorem continuous_conditionalLower (D : System ι ℝ) (x : ι) :
    Continuous (conditionalLower D x) := continuous_fold_max _ _

theorem continuous_conditionalUpper (D : System ι ℝ) (x : ι) :
    Continuous (conditionalUpper D x) := continuous_fold_min _ _

theorem continuous_update (D : System ι ℝ) (S : ℕ) (j : Fin S) (x : ι) :
    Continuous (update D S j x) := by
  apply continuous_pi
  intro y
  by_cases hy : y = x
  · subst y
    simp only [update_self, digit]
    exact (((continuous_apply x).add
      ((continuous_conditionalLower D x).const_mul _)).add
        ((continuous_conditionalUpper D x).const_mul _)).div_const _
  · simpa only [update_other D S j x y _ hy] using continuous_apply y

theorem continuous_restore (x : ι) (Y : Remaining x → ℝ) :
    Continuous (fun c => restore x c Y) := by
  apply continuous_pi
  intro y
  by_cases hy : y = x
  · subst y
    simp only [restore_self]
    exact continuous_id
  · simpa [restore, hy] using
      (continuous_const : Continuous (fun _ : ℝ => Y ⟨y, hy⟩))

/-- Integration along one actual coordinate fiber, before normalizing by
the total volume of the order region. -/
def fiberIntegral (D : System ι ℝ) (x : ι) (f : (ι → ℝ) → ℝ)
    (Y : Remaining x → ℝ) : ℝ :=
  ∫ c, (region D).indicator f (restore x c Y)

theorem fiberIntegral_eq (D : System ι ℝ) (x : ι) (hxx : D.edge x x = false)
    (f : (ι → ℝ) → ℝ) (Y : Remaining x → ℝ)
    (hY : (eraseAt D x).StrictlyFeasible Y) :
    fiberIntegral D x f Y =
      ∫ c in Ioo (fiberLower D x Y) (fiberUpper D x Y), f (restore x c Y) := by
  unfold fiberIntegral
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro c
  dsimp only
  have hc : restore x c Y ∈ region D ↔
      c ∈ Ioo (fiberLower D x Y) (fiberUpper D x Y) := by
    simpa only [region, mem_setOf_eq, mem_Ioo, hY, true_and] using
      restore_feasible_iff D x hxx Y c
  by_cases h : restore x c Y ∈ region D
  · rw [indicator_of_mem h, indicator_of_mem (hc.mp h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun hmem => h (hc.mpr hmem))]

theorem fiberIntegral_eq_zero (D : System ι ℝ) (x : ι) (hxx : D.edge x x = false)
    (f : (ι → ℝ) → ℝ) (Y : Remaining x → ℝ)
    (hY : ¬(eraseAt D x).StrictlyFeasible Y) : fiberIntegral D x f Y = 0 := by
  unfold fiberIntegral
  have he (c : ℝ) : restore x c Y ∉ region D := by
    intro h
    exact hY ((restore_feasible_iff D x hxx Y c).mp h).1
  simp only [indicator_of_notMem (he _), integral_zero]

/-- Scalar stationarity on every fiber, including empty fibers. -/
theorem fiberIntegral_stationary (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (S : ℕ) (hS : 0 < S)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (Y : Remaining x → ℝ) :
    (∑ j : Fin S, fiberIntegral D x (fun X => f (update D S j x X)) Y) / (S : ℝ) =
      fiberIntegral D x f Y := by
  by_cases hY : (eraseAt D x).StrictlyFeasible Y
  · simp_rw [fiberIntegral_eq D x hxx _ Y hY]
    by_cases hlu : fiberLower D x Y < fiberUpper D x Y
    · simp_rw [update_restore D x hxx]
      simp_rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hlu.le]
      exact digit_integral_stationary S hS hlu (fun c => f (restore x c Y))
        ((hf.comp (continuous_restore x Y)).intervalIntegrable _ _)
    · rw [Ioo_eq_empty_of_le (le_of_not_gt hlu)]
      simp
  · simp_rw [fiberIntegral_eq_zero D x hxx _ Y hY]
    simp

/-- The integrability needed by Fubini follows from actual finite volume;
it is not an additional probabilistic assumption. -/
theorem continuous_integrableOn_region (D : System ι ℝ) (f : (ι → ℝ) → ℝ)
    (hf : Continuous f) : IntegrableOn f (region D) :=
  hf.integrableOn_Icc.mono_set (region_subset_box D)

theorem fiberIntegral_integrable (D : System ι ℝ) (x : ι)
    (f : (ι → ℝ) → ℝ) (hf : IntegrableOn f (region D)) :
    Integrable (fiberIntegral D x f) := by
  have hi := (splitEquiv_measurePreserving x).integrable_comp_of_integrable
    (hf.integrable_indicator (region_open D).measurableSet)
  have he : (fun p : (Remaining x → ℝ) × ℝ =>
      (region D).indicator f (splitEquiv x p)) =
        (fun p => (region D).indicator f (restore x p.2 p.1)) := by
    funext p
    rcases p with ⟨Y, c⟩
    rw [splitEquiv_apply]
  have hp : Integrable (fun p : (Remaining x → ℝ) × ℝ =>
      (region D).indicator f (restore x p.2 p.1)) (volume.prod volume) := by
    change Integrable (fun p => (region D).indicator f (splitEquiv x p)) _ at hi
    rwa [he] at hi
  exact hp.integral_prod_left

/-- Disintegrating the region integral by the actual free-coordinate fiber. -/
theorem integral_region_fiber (D : System ι ℝ) (x : ι)
    (f : (ι → ℝ) → ℝ) (hf : IntegrableOn f (region D)) :
    (∫ X in region D, f X) = ∫ Y, fiberIntegral D x f Y := by
  rw [← integral_indicator (region_open D).measurableSet,
    ← (splitEquiv_measurePreserving x).integral_comp' ((region D).indicator f)]
  have hi := (splitEquiv_measurePreserving x).integrable_comp_of_integrable
    (hf.integrable_indicator (region_open D).measurableSet)
  change Integrable (fun p => (region D).indicator f (splitEquiv x p)) _ at hi
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  simp only [fiberIntegral, splitEquiv_apply]

/-- Averaging the actual `S` coordinate updates preserves integration on
the complete DAG order region. All intermediate endpoints are the genuine
conditional maxima and minima in the executable update. -/
theorem update_integral_stationary (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (S : ℕ) (hS : 0 < S)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) :
    (∑ j : Fin S, ∫ X in region D, f (update D S j x X)) / (S : ℝ) =
      ∫ X in region D, f X := by
  have hj (j : Fin S) : IntegrableOn (fun X => f (update D S j x X)) (region D) :=
    continuous_integrableOn_region D _ (hf.comp (continuous_update D S j x))
  simp_rw [integral_region_fiber D x _ (hj _)]
  rw [integral_region_fiber D x f (continuous_integrableOn_region D f hf)]
  calc
    _ = ∫ Y, (∑ j : Fin S,
        fiberIntegral D x (fun X => f (update D S j x X)) Y) / (S : ℝ) := by
      rw [integral_div, integral_finsetSum _
        (fun j _ => fiberIntegral_integrable D x _ (hj j))]
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (fiberIntegral_stationary D x hxx S hS f hf))

/-- The actual finite mixture of pushforwards by the digit updates. -/
def branchAverage (D : System ι ℝ) (S : ℕ) (x : ι) (μ : Measure (ι → ℝ)) :
    Measure (ι → ℝ) :=
  (S : ℝ≥0∞)⁻¹ • ∑ j : Fin S, μ.map (update D S j x)

theorem branchAverage_smul (D : System ι ℝ) (S : ℕ) (x : ι)
    (μ : Measure (ι → ℝ)) (c : ℝ≥0∞) :
    branchAverage D S x (c • μ) = c • branchAverage D S x μ := by
  simp only [branchAverage, Measure.map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- Equality of finite Borel measures upgrades continuous-test stationarity
to stationarity for every measurable event. -/
theorem update_volume_stationary (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (S : ℕ) (hS : 0 < S) :
    branchAverage D S x (volume.restrict (region D)) = volume.restrict (region D) := by
  let μ : Measure (ι → ℝ) := volume.restrict (region D)
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (lt_top_iff_ne_top.mpr (volume_ne_top D))⟩
  haveI : IsFiniteMeasure (∑ j : Fin S, μ.map (update D S j x)) := inferInstance
  haveI : IsFiniteMeasure (branchAverage D S x μ) :=
    (∑ j : Fin S, μ.map (update D S j x)).smul_finite (by
      simp only [ENNReal.inv_ne_top, Nat.cast_ne_zero]
      exact hS.ne')
  change branchAverage D S x μ = μ
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [branchAverage, integral_smul_measure,
    integral_finsetSum_measure (fun j _ => f.integrable _)]
  simp_rw [integral_map_of_stronglyMeasurable
    (continuous_update D S _ x).measurable f.continuous.stronglyMeasurable]
  simpa only [μ, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using
      update_integral_stationary D x hxx S hS f f.continuous

/-- The uniform law on the feasible order region is stationary for one
finite affine-digit update, as an equality of actual measures. -/
theorem update_uniform_stationary (D : System ι ℝ) (x : ι)
    (hxx : D.edge x x = false) (S : ℕ) (hS : 0 < S) :
    branchAverage D S x (uniformMeasure D) = uniformMeasure D := by
  rw [uniformMeasure, branchAverage_smul, update_volume_stationary D x hxx S hS]

end

end SortingAdversary.Continuous.Stationarity
