import SortingAdversary.Continuous.Density
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Linear projection bounds from convex cones

The cone argument applies to arbitrary bounded open convex regions. This
module supplies the geometric ingredient for difference events, whose fibers
are not themselves coordinate sections of an order-restriction system.
-/

namespace SortingAdversary.Continuous.ProjectionDensity

open FiniteAveraging OrderRegion Density Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slice (C : Set (ι → ℝ)) (x : ι) (t : ℝ) : Set (Remaining x → ℝ) :=
  (fun Y => restore x t Y) ⁻¹' C

def sectionVolume (C : Set (ι → ℝ)) (x : ι) (t : ℝ) : ℝ :=
  (volume (slice C x t)).toReal

theorem volume_ne_top {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hbox : C ⊆ Icc L U) : volume C ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono (μ := volume) hbox)
  rw [Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

theorem section_volume_ne_top {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hbox : C ⊆ Icc L U) (x : ι) (t : ℝ) : volume (slice C x t) ≠ ⊤ := by
  apply volume_ne_top (L := fun y : Remaining x => L y) (U := fun y => U y)
  intro Y hY
  have hb := hbox hY
  exact ⟨fun y => by simpa using hb.1 y, fun y => by simpa using hb.2 y⟩

theorem split_preimage_section (C : Set (ι → ℝ)) (x : ι) (t : ℝ) :
    (fun Y : Remaining x → ℝ => (Y, t)) ⁻¹' ((splitEquiv x) ⁻¹' C) =
      slice C x t := by
  ext Y
  simp only [mem_preimage, slice, splitEquiv_apply]

theorem section_measure_measurable {C : Set (ι → ℝ)}
    (hC : MeasurableSet C) (x : ι) : Measurable (fun t => volume (slice C x t)) := by
  have hs : MeasurableSet ((splitEquiv x) ⁻¹' C) := hC.preimage (splitEquiv x).measurable
  simpa only [split_preimage_section] using
    (measurable_measure_prodMk_right (μ := volume) hs)

theorem lintegral_section {C : Set (ι → ℝ)} (hC : MeasurableSet C) (x : ι) :
    (∫⁻ t, volume (slice C x t)) = volume C := by
  have hs : MeasurableSet ((splitEquiv x) ⁻¹' C) := hC.preimage (splitEquiv x).measurable
  have hm := (splitEquiv_measurePreserving x).measure_preimage hC.nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hs] at hm
  simpa only [split_preimage_section] using hm

theorem sectionVolume_integrable {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : MeasurableSet C) (hbox : C ⊆ Icc L U) (x : ι) :
    Integrable (sectionVolume C x) := by
  exact integrable_toReal_of_lintegral_ne_top (section_measure_measurable hC x).aemeasurable
    (by rw [lintegral_section hC]; exact volume_ne_top hbox)

theorem integral_sectionVolume {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : MeasurableSet C) (hbox : C ⊆ Icc L U) (x : ι) :
    (∫ t, sectionVolume C x t) = (volume C).toReal := by
  change (∫ t, (volume (slice C x t)).toReal) = _
  rw [integral_toReal (section_measure_measurable hC x).aemeasurable
    (Filter.Eventually.of_forall fun t => lt_top_iff_ne_top.mpr
      (section_volume_ne_top hbox x t)), lintegral_section hC]

/-- A cone to any point of the closure of the convex body. -/
theorem homothety_section_subset {C : Set (ι → ℝ)}
    (hC : IsOpen C) (hc : Convex ℝ C) (x : ι) {Q : ι → ℝ}
    (hQ : Q ∈ closure C) (t : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    AffineMap.homothety (fun y : Remaining x => Q y) a '' slice C x t ⊆
      slice C x (a * t + (1 - a) * Q x) := by
  rintro _ ⟨Y, hY, rfl⟩
  have hY' : restore x t Y ∈ C := hY
  have hm := hc.combo_interior_closure_mem_interior
    (by simpa only [hC.interior_eq] using hY') hQ ha
    (sub_nonneg.mpr ha1) (by ring)
  rw [hC.interior_eq] at hm
  have he : restore x (a * t + (1 - a) * Q x)
      (AffineMap.homothety (fun y : Remaining x => Q y) a Y) =
        a • restore x t Y + (1 - a) • Q := by
    funext y
    by_cases hy : y = x
    · subst y
      simp
    · simp only [restore, dif_neg hy, AffineMap.homothety_apply, vsub_eq_sub,
        vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
  change restore x (a * t + (1 - a) * Q x)
    (AffineMap.homothety (fun y : Remaining x => Q y) a Y) ∈ C
  rwa [he]

theorem section_transport {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {Q : ι → ℝ} (hQ : Q ∈ closure C) (t : ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ Fintype.card (Remaining x) * sectionVolume C x t ≤
      sectionVolume C x (a * t + (1 - a) * Q x) := by
  have hm := measure_mono (μ := volume) (homothety_section_subset hC hc x hQ t ha ha1)
  rw [Measure.addHaar_image_homothety volume, Module.finrank_fintype_fun_eq_card,
    abs_of_nonneg (pow_nonneg ha.le _)] at hm
  have hr := ENNReal.toReal_mono (section_volume_ne_top hbox x _) hm
  simpa only [sectionVolume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha.le _)] using hr

theorem section_towards_upper {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {Q : ι → ℝ} (hQ : Q ∈ closure C) {t s : ℝ}
    (hts : t < s) (hs : s < Q x) :
    ((Q x - s) / (Q x - t)) ^ Fintype.card (Remaining x) * sectionVolume C x t ≤
      sectionVolume C x s := by
  have hd : 0 < Q x - t := sub_pos.mpr (hts.trans hs)
  have ha : 0 < (Q x - s) / (Q x - t) := div_pos (sub_pos.mpr hs) hd
  have ha1 : (Q x - s) / (Q x - t) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have he : (Q x - s) / (Q x - t) * t +
      (1 - (Q x - s) / (Q x - t)) * Q x = s := by field_simp; ring
  simpa only [he] using section_transport hC hc hbox x hQ t ha ha1

theorem section_towards_lower {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {Q : ι → ℝ} (hQ : Q ∈ closure C) {t s : ℝ}
    (hs : Q x < s) (hst : s < t) :
    ((s - Q x) / (t - Q x)) ^ Fintype.card (Remaining x) * sectionVolume C x t ≤
      sectionVolume C x s := by
  have hd : 0 < t - Q x := sub_pos.mpr (hs.trans hst)
  have ha : 0 < (s - Q x) / (t - Q x) := div_pos (sub_pos.mpr hs) hd
  have ha1 : (s - Q x) / (t - Q x) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have he : (s - Q x) / (t - Q x) * t +
      (1 - (s - Q x) / (t - Q x)) * Q x = s := by field_simp; ring
  simpa only [he] using section_transport hC hc hbox x hQ t ha ha1

theorem lower_cone_integral {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {Q : ι → ℝ} (hQ : Q ∈ closure C) {t : ℝ} (ht : Q x < t) :
    (t - Q x) / (Fintype.card (Remaining x) + 1 : ℝ) * sectionVolume C x t ≤
      ∫ s in Q x..t, sectionVolume C x s := by
  have hcont : Continuous (fun s : ℝ =>
      ((s - Q x) / (t - Q x)) ^ Fintype.card (Remaining x) * sectionVolume C x t) :=
    (((continuous_id.sub continuous_const).div_const _).pow _).mul_const _
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo ht.le
    (hcont.intervalIntegrable _ _)
    (sectionVolume_integrable hC.measurableSet hbox x).intervalIntegrable
    (fun s hs => section_towards_lower hC hc hbox x hQ hs.1 hs.2)
  rwa [intervalIntegral.integral_mul_const, integral_lower_cone _ _ ht] at hi

theorem upper_cone_integral {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {Q : ι → ℝ} (hQ : Q ∈ closure C) {t : ℝ} (ht : t < Q x) :
    (Q x - t) / (Fintype.card (Remaining x) + 1 : ℝ) * sectionVolume C x t ≤
      ∫ s in t..Q x, sectionVolume C x s := by
  have hcont : Continuous (fun s : ℝ =>
      ((Q x - s) / (Q x - t)) ^ Fintype.card (Remaining x) * sectionVolume C x t) :=
    (((continuous_const.sub continuous_id).div_const _).pow _).mul_const _
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo ht.le
    (hcont.intervalIntegrable _ _)
    (sectionVolume_integrable hC.measurableSet hbox x).intervalIntegrable
    (fun s hs => section_towards_upper hC hc hbox x hQ hs.1 hs.2)
  rwa [intervalIntegral.integral_mul_const, integral_upper_cone _ _ ht] at hi

theorem interval_integral_le_volume {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : MeasurableSet C) (hbox : C ⊆ Icc L U) (x : ι) {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, sectionVolume C x s) ≤ (volume C).toReal := by
  rw [intervalIntegral.integral_of_le hab, ← integral_sectionVolume hC hbox x]
  exact setIntegral_le_integral (sectionVolume_integrable hC hbox x)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)

/-- Any two points of the closure give a lower bound on the projection
width, hence an upper bound on every section, including sections outside
the interval between the chosen points. -/
theorem section_upper_of_pair {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {P Q : ι → ℝ} (hP : P ∈ closure C) (hQ : Q ∈ closure C)
    (hPQ : P x < Q x) (t : ℝ) :
    (Q x - P x) * sectionVolume C x t ≤
      (Fintype.card (Remaining x) + 1 : ℝ) * (volume C).toReal := by
  let m : ℝ := Fintype.card (Remaining x) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : 0 ≤ sectionVolume C x t := ENNReal.toReal_nonneg
  have hmain : (Q x - P x) / m * sectionVolume C x t ≤ (volume C).toReal := by
    by_cases htlo : t ≤ P x
    · have hcone := (upper_cone_integral hC hc hbox x hQ (htlo.trans_lt hPQ)).trans
        (interval_integral_le_volume hC.measurableSet hbox x (htlo.trans hPQ.le))
      exact (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) hm.le) hn).trans hcone
    · by_cases hthi : Q x ≤ t
      · have hcone := (lower_cone_integral hC hc hbox x hP (hPQ.trans_le hthi)).trans
          (interval_integral_le_volume hC.measurableSet hbox x (hPQ.le.trans hthi))
        exact (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hm.le) hn).trans hcone
      · have hl := lower_cone_integral hC hc hbox x hP (lt_of_not_ge htlo)
        have hu := upper_cone_integral hC hc hbox x hQ (lt_of_not_ge hthi)
        have hs := add_le_add hl hu
        rw [intervalIntegral.integral_add_adjacent_intervals
          (sectionVolume_integrable hC.measurableSet hbox x).intervalIntegrable
          (sectionVolume_integrable hC.measurableSet hbox x).intervalIntegrable] at hs
        calc
          _ = (t - P x) / m * sectionVolume C x t +
              (Q x - t) / m * sectionVolume C x t := by ring
          _ ≤ _ := hs
          _ ≤ _ := interval_integral_le_volume hC.measurableSet hbox x hPQ.le
  have hmul := (div_le_iff₀ hm).mp (show
      ((Q x - P x) * sectionVolume C x t) / m ≤ (volume C).toReal by
        simpa only [div_mul_eq_mul_div] using hmain)
  simpa only [m, mul_comm] using hmul

/-- Fubini identifies coordinate band volumes with the integrated sections. -/
theorem band_volume {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : MeasurableSet C) (hbox : C ⊆ Icc L U) (x : ι)
    (I : Set ℝ) (hI : MeasurableSet I) :
    (volume (C ∩ {X | X x ∈ I})).toReal = ∫ t in I, sectionVolume C x t := by
  have hband : MeasurableSet (C ∩ {X | X x ∈ I}) :=
    hC.inter (hI.preimage (measurable_pi_apply x))
  have hb : C ∩ {X | X x ∈ I} ⊆ Icc L U := inter_subset_left.trans hbox
  have he (t : ℝ) : sectionVolume (C ∩ {X | X x ∈ I}) x t =
      I.indicator (sectionVolume C x) t := by
    by_cases ht : t ∈ I
    · have hs : slice (C ∩ {X | X x ∈ I}) x t = slice C x t := by
        ext Y
        simp only [slice, mem_preimage, mem_inter_iff, mem_setOf_eq, restore_self, ht, and_true]
      simp only [sectionVolume, hs, indicator_of_mem ht]
    · have hs : slice (C ∩ {X | X x ∈ I}) x t = ∅ := by
        ext Y
        simp only [slice, mem_preimage, mem_inter_iff, mem_setOf_eq, restore_self, ht,
          and_false, mem_empty_iff_false]
      simp only [sectionVolume, hs, measure_empty, ENNReal.toReal_zero, indicator_of_notMem ht]
  rw [← integral_sectionVolume hband hb x]
  simp_rw [he]
  exact integral_indicator hI

/-- A convex body's mass in a coordinate band is at most its dimension
times the relative band length. The width may be certified by any two
closure points. -/
theorem band_volume_le {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x : ι) {P Q : ι → ℝ} (hP : P ∈ closure C) (hQ : Q ∈ closure C)
    (hPQ : P x < Q x) {a b : ℝ} (hab : a ≤ b) :
    (volume (C ∩ {X | X x ∈ Icc a b})).toReal ≤
      (Fintype.card (Remaining x) + 1 : ℝ) * (b - a) / (Q x - P x) *
        (volume C).toReal := by
  have hW : 0 < Q x - P x := sub_pos.mpr hPQ
  have hs (t : ℝ) : sectionVolume C x t ≤
      (Fintype.card (Remaining x) + 1 : ℝ) * (volume C).toReal / (Q x - P x) := by
    apply (le_div_iff₀ hW).mpr
    simpa only [mul_comm] using section_upper_of_pair hC hc hbox x hP hQ hPQ t
  rw [band_volume hC.measurableSet hbox x _ measurableSet_Icc]
  have hi := setIntegral_mono_on
    (sectionVolume_integrable hC.measurableSet hbox x).integrableOn
    (integrableOn_const (by simp : volume (Icc a b) ≠ ⊤))
    measurableSet_Icc (fun t _ => hs t)
  have he : (∫ _t in Icc a b,
      (Fintype.card (Remaining x) + 1 : ℝ) * (volume C).toReal / (Q x - P x)) =
      (Fintype.card (Remaining x) + 1 : ℝ) * (b - a) / (Q x - P x) *
        (volume C).toReal := by
    simp only [setIntegral_const, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
      smul_eq_mul, Measure.real_def]
    ring
  exact hi.trans_eq he

/-- Subtract one coordinate from another. Its determinant is exactly one. -/
def differenceEquiv (x y : ι) (hxy : x ≠ y) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.transvection (f := -(LinearMap.proj y : (ι → ℝ) →ₗ[ℝ] ℝ))
    (v := Pi.single x 1) (by simp [hxy, hxy.symm])

theorem differenceEquiv_apply (x y : ι) (hxy : x ≠ y) (X : ι → ℝ) :
    differenceEquiv x y hxy X = Function.update X x (X x - X y) := by
  funext z
  by_cases hz : z = x
  · subst z
    simp [differenceEquiv, LinearMap.transvection.apply, sub_eq_add_neg]
  · simp [differenceEquiv, LinearMap.transvection.apply, hz, Ne.symm hz]

@[simp] theorem differenceEquiv_self (x y : ι) (hxy : x ≠ y) (X : ι → ℝ) :
    differenceEquiv x y hxy X x = X x - X y := by rw [differenceEquiv_apply]; simp

theorem differenceEquiv_volume (x y : ι) (hxy : x ≠ y) (A : Set (ι → ℝ)) :
    volume (differenceEquiv x y hxy '' A) = volume A := by
  change volume ((differenceEquiv x y hxy).toLinearMap '' A) = volume A
  rw [Measure.addHaar_image_linearMap]
  simp [differenceEquiv, hxy.symm]

/-- The general convex projection estimate for a coordinate difference,
certified by two points of the body's closure. -/
theorem difference_band_volume_le {C : Set (ι → ℝ)} {L U : ι → ℝ}
    (hC : IsOpen C) (hc : Convex ℝ C) (hbox : C ⊆ Icc L U)
    (x y : ι) (hxy : x ≠ y) {P Q : ι → ℝ}
    (hP : P ∈ closure C) (hQ : Q ∈ closure C)
    (hPQ : P x - P y < Q x - Q y) {a b : ℝ} (hab : a ≤ b) :
    (volume (C ∩ {X | X x - X y ∈ Icc a b})).toReal ≤
      (Fintype.card (Remaining x) + 1 : ℝ) * (b - a) /
        ((Q x - Q y) - (P x - P y)) * (volume C).toReal := by
  let e := differenceEquiv x y hxy
  let C' := e '' C
  have ho : IsOpen C' := e.toContinuousLinearEquiv.toHomeomorph.isOpenMap C hC
  have hv : Convex ℝ C' := hc.linear_image e.toLinearMap
  have hb : C' ⊆ Icc (Function.update L x (L x - U y))
      (Function.update U x (U x - L y)) := by
    rintro _ ⟨X, hX, rfl⟩
    have hx := hbox hX
    constructor <;> intro z <;> by_cases hz : z = x
    · subst z
      simp only [e, differenceEquiv_self, Function.update_self]
      linarith [hx.1 x, hx.2 y]
    · simpa only [e, differenceEquiv_apply, Function.update_of_ne hz] using hx.1 z
    · subst z
      simp only [e, differenceEquiv_self, Function.update_self]
      linarith [hx.2 x, hx.1 y]
    · simpa only [e, differenceEquiv_apply, Function.update_of_ne hz] using hx.2 z
  have hp : e P ∈ closure C' := image_closure_subset_closure_image
    e.toContinuousLinearEquiv.continuous ⟨P, hP, rfl⟩
  have hq : e Q ∈ closure C' := image_closure_subset_closure_image
    e.toContinuousLinearEquiv.continuous ⟨Q, hQ, rfl⟩
  have hwidth : e P x < e Q x := by simpa only [e, differenceEquiv_self] using hPQ
  have hbound := band_volume_le ho hv hb x hp hq hwidth hab
  have hevent : C' ∩ {X | X x ∈ Icc a b} =
      e '' (C ∩ {X | X x - X y ∈ Icc a b}) := by
    ext Z
    constructor
    · rintro ⟨⟨X, hX, rfl⟩, hZ⟩
      exact ⟨X, ⟨hX, by simpa only [mem_setOf_eq, e, differenceEquiv_self] using hZ⟩, rfl⟩
    · rintro ⟨X, ⟨hX, hZ⟩, rfl⟩
      exact ⟨⟨X, hX, rfl⟩, by simpa only [mem_setOf_eq, e, differenceEquiv_self] using hZ⟩
  rw [hevent] at hbound
  simpa only [C', e, differenceEquiv_volume, differenceEquiv_self] using hbound

end

end SortingAdversary.Continuous.ProjectionDensity
