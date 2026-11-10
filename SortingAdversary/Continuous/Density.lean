import SortingAdversary.Continuous.OrderRegion
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous section comparisons from explicit homotheties

For normalized order constraints the vectors of all lower endpoints and all
upper endpoints are weakly feasible. Mixing a strictly feasible assignment
with either vector, with positive weight on the strict assignment, remains
strictly feasible. On a coordinate section this is a homothety in the other
coordinates. Its exact Lebesgue volume scaling proves the manuscript's cone
comparison inequalities for actual order regions.

The final dimension-reduced density estimates additionally require Fubini and
conditioning on incomparable coordinates; those conclusions are not assumed
or claimed here.
-/

namespace SortingAdversary.Continuous.Density

open FiniteAveraging OrderRegion Set MeasureTheory
open scoped Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem endpoints_weaklyFeasible (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ x, D.lower x ≤ D.upper x) :
    D.WeaklyFeasible D.lower ∧ D.WeaklyFeasible D.upper := by
  exact ⟨⟨fun x => ⟨le_rfl, hw x⟩, fun x y hxy => (hD x y hxy).1⟩,
    ⟨fun x => ⟨hw x, le_rfl⟩, fun x y hxy => (hD x y hxy).2⟩⟩

/-- A positive proportion of a strict assignment makes every inequality
strict even when the other assignment lies on several boundary faces. -/
theorem strict_mix_weak (D : System ι ℝ) {X Y : ι → ℝ}
    (hX : D.StrictlyFeasible X) (hY : D.WeaklyFeasible Y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    D.StrictlyFeasible (fun x => a * X x + b * Y x) := by
  constructor
  · intro x
    have h₁ := mul_pos ha (sub_pos.mpr (hX.1 x).1)
    have h₂ := mul_nonneg hb (sub_nonneg.mpr (hY.1 x).1)
    have h₃ := mul_pos ha (sub_pos.mpr (hX.1 x).2)
    have h₄ := mul_nonneg hb (sub_nonneg.mpr (hY.1 x).2)
    have hl : a * D.lower x + b * D.lower x = D.lower x := by
      rw [← add_mul, hab, one_mul]
    have hu : a * D.upper x + b * D.upper x = D.upper x := by
      rw [← add_mul, hab, one_mul]
    constructor <;> nlinarith
  · intro x y hxy
    have h₁ := mul_pos ha (sub_pos.mpr (hX.2 x y hxy))
    have h₂ := mul_nonneg hb (sub_nonneg.mpr (hY.2 x y hxy))
    nlinarith

/-- Cone transport between genuine coordinate sections. -/
theorem homothety_section_subset (D : System ι ℝ) (x : ι)
    (Q : ι → ℝ) (hQ : D.WeaklyFeasible Q) (t : ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    AffineMap.homothety (fun y : Remaining x => Q y) a '' sectionAt D x t ⊆
      sectionAt D x (a * t + (1 - a) * Q x) := by
  rintro _ ⟨Y, hY, rfl⟩
  have hm := strict_mix_weak D hY hQ ha (sub_nonneg.mpr ha1) (by ring)
  have heq : restore x (a * t + (1 - a) * Q x)
      (AffineMap.homothety (fun y : Remaining x => Q y) a Y) =
      (fun y => a * restore x t Y y + (1 - a) * Q y) := by
    funext y
    by_cases hy : y = x
    · subst y
      simp
    · simp only [restore, dif_neg hy, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
        Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
  change D.StrictlyFeasible _
  rwa [heq]

theorem section_volume_ne_top (D : System ι ℝ) (x : ι) (c : ℝ) :
    volume (sectionAt D x c) ≠ ⊤ := by
  have hs : sectionAt D x c ⊆
      Icc (fun y : Remaining x => D.lower y) (fun y : Remaining x => D.upper y) := by
    intro Y hY
    constructor
    · intro y
      simpa using (hY.1 y).1.le
    · intro y
      simpa using (hY.1 y).2.le
  apply ne_top_of_le_ne_top _ (measure_mono (μ := volume) hs)
  rw [Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun y _ => ENNReal.ofReal_ne_top

theorem sectionVolume_nonneg (D : System ι ℝ) (x : ι) (c : ℝ) :
    0 ≤ sectionVolume D x c := ENNReal.toReal_nonneg

/-- Separate one coordinate, retaining the product Lebesgue measure. -/
def splitEquiv (x : ι) : ((Remaining x → ℝ) × ℝ) ≃ᵐ (ι → ℝ) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Remaining x) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe x))

theorem splitEquiv_apply (x : ι) (Y : Remaining x → ℝ) (c : ℝ) :
    splitEquiv x (Y, c) = restore x c Y := by
  funext y
  by_cases hy : y = x
  · subst y
    rw [restore_self]
    have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.optionSubtypeNe x)
      (β := fun _ : ι => ℝ)
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Remaining x) => ℝ)).symm (Y, c))
      none
    change (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe x))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Remaining x) => ℝ)).symm
        (Y, c)) x = c
    have hn : (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Remaining x) => ℝ)).symm (Y, c) none = c := rfl
    simpa only [Equiv.optionSubtypeNe_none, hn] using h
  · have h := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.optionSubtypeNe x)
      (β := fun _ : ι => ℝ)
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Remaining x) => ℝ)).symm (Y, c))
      (some ⟨y, hy⟩)
    change (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe x))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Remaining x) => ℝ)).symm
        (Y, c)) y = restore x c Y y
    have hn : (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Remaining x) => ℝ)).symm (Y, c) (some ⟨y, hy⟩) =
          Y ⟨y, hy⟩ := rfl
    simpa only [Equiv.optionSubtypeNe_some, restore, dif_neg hy, hn] using h

theorem splitEquiv_measurePreserving (x : ι) :
    MeasurePreserving (splitEquiv x) volume volume := by
  have hopt : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Remaining x) => ℝ)).symm
      volume volume :=
    ⟨MeasurableEquiv.measurable _,
      Measure.pi_map_piOptionEquivProd (fun _ : Option (Remaining x) =>
        (volume : Measure ℝ))⟩
  exact (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ)
    (Equiv.optionSubtypeNe x)).comp hopt

theorem split_preimage_section (D : System ι ℝ) (x : ι) (c : ℝ) :
    (fun Y : Remaining x → ℝ => (Y, c)) ⁻¹' ((splitEquiv x) ⁻¹' region D) =
      sectionAt D x c := by
  ext Y
  simp only [mem_preimage, region, sectionAt, mem_setOf_eq, splitEquiv_apply]

theorem section_measure_measurable (D : System ι ℝ) (x : ι) :
    Measurable (fun c => volume (sectionAt D x c)) := by
  have hs : MeasurableSet ((splitEquiv x) ⁻¹' region D) :=
    (region_open D).measurableSet.preimage (splitEquiv x).measurable
  simpa only [split_preimage_section] using
    (measurable_measure_prodMk_right (μ := volume) hs)

/-- Fubini for the actual strict coordinate sections. -/
theorem lintegral_section (D : System ι ℝ) (x : ι) :
    (∫⁻ c, volume (sectionAt D x c)) = volume (region D) := by
  have hs : MeasurableSet ((splitEquiv x) ⁻¹' region D) :=
    (region_open D).measurableSet.preimage (splitEquiv x).measurable
  have hm := (splitEquiv_measurePreserving x).measure_preimage
    (region_open D).measurableSet.nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hs] at hm
  simpa only [split_preimage_section] using hm

theorem sectionVolume_integrable (D : System ι ℝ) (x : ι) :
    Integrable (sectionVolume D x) := by
  exact integrable_toReal_of_lintegral_ne_top
    (section_measure_measurable D x).aemeasurable
    (by rw [lintegral_section]; exact volume_ne_top D)

theorem integral_sectionVolume (D : System ι ℝ) (x : ι) :
    (∫ c, sectionVolume D x c) = nodeVolume D := by
  change (∫ c, (volume (sectionAt D x c)).toReal) = (volume (region D)).toReal
  rw [integral_toReal
    (section_measure_measurable D x).aemeasurable
    (Filter.Eventually.of_forall fun c => lt_top_iff_ne_top.mpr (section_volume_ne_top D x c)),
    lintegral_section]

/-- The pointwise section density really integrates to one. -/
theorem integral_density (D : System ι ℝ) (x : ι) (hV : 0 < nodeVolume D) :
    (∫ c, density D x c) = 1 := by
  simp only [density, integral_div, integral_sectionVolume, div_self hV.ne']

theorem integral_sectionVolume_interval (D : System ι ℝ) (x : ι) :
    (∫ c in Ioo (D.lower x) (D.upper x), sectionVolume D x c) = nodeVolume D := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_sectionVolume D x
  · intro c hc
    simp only [mem_Ioo] at hc
    simp only [sectionVolume, section_empty_of_outside D x c hc, measure_empty,
      ENNReal.toReal_zero]

/-- The scale exponent is the number of coordinates remaining in the section,
so no full-dimensional hyperplane measure occurs in this calculation. -/
theorem sectionVolume_transport (D : System ι ℝ) (x : ι)
    (Q : ι → ℝ) (hQ : D.WeaklyFeasible Q) (t : ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ Fintype.card (Remaining x) * sectionVolume D x t ≤
      sectionVolume D x (a * t + (1 - a) * Q x) := by
  have hm := measure_mono (μ := volume) (homothety_section_subset D x Q hQ t ha ha1)
  rw [Measure.addHaar_image_homothety volume] at hm
  rw [Module.finrank_fintype_fun_eq_card,
    abs_of_nonneg (pow_nonneg ha.le _)] at hm
  have hreal := ENNReal.toReal_mono (section_volume_ne_top D x _) hm
  simpa only [sectionVolume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha.le _)] using hreal

/-- Moving a section towards the upper endpoint loses at most its cone factor. -/
theorem sectionVolume_towards_upper (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ y, D.lower y ≤ D.upper y) (x : ι) {t s : ℝ}
    (hts : t < s) (hs : s < D.upper x) :
    ((D.upper x - s) / (D.upper x - t)) ^ Fintype.card (Remaining x) *
        sectionVolume D x t ≤ sectionVolume D x s := by
  have hden : 0 < D.upper x - t := sub_pos.mpr (hts.trans hs)
  have ha : 0 < (D.upper x - s) / (D.upper x - t) :=
    div_pos (sub_pos.mpr hs) hden
  have ha1 : (D.upper x - s) / (D.upper x - t) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have heq : (D.upper x - s) / (D.upper x - t) * t +
      (1 - (D.upper x - s) / (D.upper x - t)) * D.upper x = s := by
    field_simp
    <;> ring
  simpa only [heq] using sectionVolume_transport D x D.upper
    (endpoints_weaklyFeasible D hD hw).2 t ha ha1

/-- The corresponding cone factor towards the lower endpoint. -/
theorem sectionVolume_towards_lower (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ y, D.lower y ≤ D.upper y) (x : ι) {t s : ℝ}
    (hs : D.lower x < s) (hst : s < t) :
    ((s - D.lower x) / (t - D.lower x)) ^ Fintype.card (Remaining x) *
        sectionVolume D x t ≤ sectionVolume D x s := by
  have hden : 0 < t - D.lower x := sub_pos.mpr (hs.trans hst)
  have ha : 0 < (s - D.lower x) / (t - D.lower x) :=
    div_pos (sub_pos.mpr hs) hden
  have ha1 : (s - D.lower x) / (t - D.lower x) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have heq : (s - D.lower x) / (t - D.lower x) * t +
      (1 - (s - D.lower x) / (t - D.lower x)) * D.lower x = s := by
    field_simp
    <;> ring
  simpa only [heq] using sectionVolume_transport D x D.lower
    (endpoints_weaklyFeasible D hD hw).1 t ha ha1

/-- Every section in the middle half has at least a `4^(-dimension)`
fraction of any other section. This is a statement about actual volumes. -/
theorem central_section_comparison (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ y, D.lower y < D.upper y) (x : ι) {t s : ℝ}
    (ht : D.lower x < t ∧ t < D.upper x)
    (hs : D.lower x + (D.upper x - D.lower x) / 4 ≤ s ∧
      s ≤ D.upper x - (D.upper x - D.lower x) / 4) :
    (1 / 4 : ℝ) ^ Fintype.card (Remaining x) * sectionVolume D x t ≤
      sectionVolume D x s := by
  have hslo : D.lower x < s := by linarith [hw x]
  have hshi : s < D.upper x := by linarith [hw x]
  rcases lt_trichotomy t s with hts | rfl | hst
  · have hden : 0 < D.upper x - t := sub_pos.mpr ht.2
    have hquarter : (1 / 4 : ℝ) ≤ (D.upper x - s) / (D.upper x - t) := by
      apply (le_div_iff₀ hden).mpr
      linarith
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hquarter _) (sectionVolume_nonneg D x t)).trans
      (sectionVolume_towards_upper D hD (fun y => (hw y).le) x hts hshi)
  · exact mul_le_of_le_one_left (sectionVolume_nonneg D x t)
      (pow_le_one₀ (by norm_num) (by norm_num))
  · have hden : 0 < t - D.lower x := sub_pos.mpr ht.1
    have hquarter : (1 / 4 : ℝ) ≤ (s - D.lower x) / (t - D.lower x) := by
      apply (le_div_iff₀ hden).mpr
      linarith
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hquarter _) (sectionVolume_nonneg D x t)).trans
      (sectionVolume_towards_lower D hD (fun y => (hw y).le) x hslo hst)

/-- A fully derived pointwise middle-half density bound in the actual number
of free coordinates. The paper's comparable-coordinate improvement applies
this geometric estimate after conditioning. -/
theorem central_density_lower (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ y, D.lower y < D.upper y) (hV : 0 < nodeVolume D)
    (x : ι) {s : ℝ}
    (hs : D.lower x + (D.upper x - D.lower x) / 4 ≤ s ∧
      s ≤ D.upper x - (D.upper x - D.lower x) / 4) :
    (1 / 4 : ℝ) ^ Fintype.card (Remaining x) / (D.upper x - D.lower x) ≤
      density D x s := by
  have hi := setIntegral_mono_on
    ((sectionVolume_integrable D x).integrableOn.const_mul
      ((1 / 4 : ℝ) ^ Fintype.card (Remaining x)))
    (integrableOn_const (by simp : volume (Ioo (D.lower x) (D.upper x)) ≠ ⊤))
    measurableSet_Ioo
    (fun t ht => central_section_comparison D hD hw x ht hs)
  have hconst : (∫ _t in Ioo (D.lower x) (D.upper x), sectionVolume D x s) =
      (D.upper x - D.lower x) * sectionVolume D x s := by
    simp [Real.volume_Ioo, (sub_pos.mpr (hw x)).le]
  rw [integral_const_mul, integral_sectionVolume_interval, hconst] at hi
  unfold density
  apply (div_le_div_iff₀ (sub_pos.mpr (hw x)) hV).mpr
  simpa only [mul_comm] using hi

theorem integral_lower_cone (l t : ℝ) (hlt : l < t) (m : ℕ) :
    (∫ s in l..t, ((s - l) / (t - l)) ^ m) = (t - l) / (m + 1 : ℝ) := by
  have hden : t - l ≠ 0 := (sub_pos.mpr hlt).ne'
  have h := intervalIntegral.integral_comp_div_sub (fun z : ℝ => z ^ m) hden
    (l / (t - l)) (a := l) (b := t)
  simpa only [← sub_div, sub_self, zero_div, div_self hden,
    integral_pow, one_pow, zero_pow (Nat.succ_ne_zero m),
    sub_zero, smul_eq_mul, mul_one_div] using h

theorem integral_upper_cone (t r : ℝ) (htr : t < r) (m : ℕ) :
    (∫ s in t..r, ((r - s) / (r - t)) ^ m) = (r - t) / (m + 1 : ℝ) := by
  have hden : r - t ≠ 0 := (sub_pos.mpr htr).ne'
  have h := intervalIntegral.integral_comp_sub_div (fun z : ℝ => z ^ m) hden
    (r / (r - t)) (a := t) (b := r)
  simpa only [← sub_div, sub_self, zero_div, div_self hden,
    integral_pow, one_pow, zero_pow (Nat.succ_ne_zero m),
    sub_zero, smul_eq_mul, mul_one_div] using h

/-- Integrating the two actual section cones gives the pointwise upper bound
in the total number of free coordinates, with no assumed density estimate. -/
theorem density_upper (D : System ι ℝ) (hD : Normalized D)
    (hw : ∀ y, D.lower y < D.upper y) (hV : 0 < nodeVolume D)
    (x : ι) {t : ℝ} (ht : D.lower x < t ∧ t < D.upper x) :
    density D x t ≤ (Fintype.card (Remaining x) + 1 : ℝ) /
      (D.upper x - D.lower x) := by
  let m := Fintype.card (Remaining x)
  have hcl : Continuous (fun s : ℝ =>
      ((s - D.lower x) / (t - D.lower x)) ^ m * sectionVolume D x t) :=
    (((continuous_id.sub continuous_const).div_const _).pow _).mul_const _
  have hcu : Continuous (fun s : ℝ =>
      ((D.upper x - s) / (D.upper x - t)) ^ m * sectionVolume D x t) :=
    (((continuous_const.sub continuous_id).div_const _).pow _).mul_const _
  have hl := intervalIntegral.integral_mono_on_of_le_Ioo ht.1.le
    (hcl.intervalIntegrable _ _) (sectionVolume_integrable D x).intervalIntegrable
    (fun s hs => sectionVolume_towards_lower D hD (fun y => (hw y).le) x hs.1 hs.2)
  have hu := intervalIntegral.integral_mono_on_of_le_Ioo ht.2.le
    (hcu.intervalIntegrable _ _) (sectionVolume_integrable D x).intervalIntegrable
    (fun s hs => sectionVolume_towards_upper D hD (fun y => (hw y).le) x hs.1 hs.2)
  rw [intervalIntegral.integral_mul_const, integral_lower_cone _ _ ht.1] at hl
  rw [intervalIntegral.integral_mul_const, integral_upper_cone _ _ ht.2] at hu
  have hsum := add_le_add hl hu
  rw [intervalIntegral.integral_add_adjacent_intervals
    (sectionVolume_integrable D x).intervalIntegrable
    (sectionVolume_integrable D x).intervalIntegrable,
    intervalIntegral.integral_of_le (hw x).le,
    integral_Ioc_eq_integral_Ioo, integral_sectionVolume_interval] at hsum
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hprod : (D.upper x - D.lower x) * sectionVolume D x t ≤
      nodeVolume D * (m + 1 : ℝ) := by
    apply (div_le_iff₀ hm).mp
    calc
      _ = (t - D.lower x) / (m + 1 : ℝ) * sectionVolume D x t +
          (D.upper x - t) / (m + 1 : ℝ) * sectionVolume D x t := by ring
      _ ≤ _ := hsum
  unfold density
  apply (div_le_div_iff₀ hV (sub_pos.mpr (hw x))).mpr
  simpa only [mul_comm] using hprod

end SortingAdversary.Continuous.Density
