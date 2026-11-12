import SortingAdversary.Continuous.Density

/-!
# Density bounds using only comparable coordinates

An upper cone need only move the descendants of the selected coordinate;
its ancestors and incomparable coordinates remain fixed. A lower cone moves
only ancestors. The diagonal affine maps have exact Jacobians determined by
these smaller sets. This proves the manuscript's dimension reduction directly
for order regions, without introducing an abstract conditional density.
-/

namespace SortingAdversary.Continuous.ComparableDensity

open FiniteAveraging OrderRegion Density Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A homothety on selected coordinates, fixing all other coordinates. -/
def maskedHomothety (U : ι → Prop) [DecidablePred U] (Q : ι → ℝ) (a : ℝ)
    (X : ι → ℝ) : ι → ℝ :=
  fun y => if U y then a * X y + (1 - a) * Q y else X y

theorem maskedHomothety_volume (U : ι → Prop) [DecidablePred U]
    (Q : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (A : Set (ι → ℝ)) :
    volume (maskedHomothety U Q a '' A) =
      ENNReal.ofReal (a ^ (Finset.univ.filter U).card) * volume A := by
  let k : ι → ℝ := fun y => if U y then a else 1
  let b : ι → ℝ := fun y => if U y then (1 - a) * Q y else 0
  let L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.toLin' (Matrix.diagonal k)
  have he : maskedHomothety U Q a = (fun Z => Z + b) ∘ L := by
    funext X y
    simp only [maskedHomothety, Function.comp_apply, Pi.add_apply,
      L, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    dsimp [k, b]
    split_ifs <;> ring
  rw [he, image_comp, image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_diagonal]
  have hk : (∏ y, k y) = a ^ (Finset.univ.filter U).card := by
    simp only [k, ← Finset.prod_filter, Finset.prod_const]
  rw [hk, abs_of_nonneg (pow_nonneg ha _)]

/-- An upward closed set can be moved towards its upper endpoints while
every coordinate outside it is held fixed. -/
theorem raise_feasible (D : System ι ℝ) (hD : Normalized D)
    (U : ι → Prop) [DecidablePred U]
    (hU : ∀ y z, U y → D.edge y z = true → U z)
    {X : ι → ℝ} (hX : D.StrictlyFeasible X)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    D.StrictlyFeasible (maskedHomothety U D.upper a X) := by
  have hab : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hinc (y : ι) : X y ≤ a * X y + (1 - a) * D.upper y := by
    have := mul_nonneg hab (sub_nonneg.mpr (hX.1 y).2.le)
    nlinarith
  constructor
  · intro y
    by_cases hy : U y
    · simp only [maskedHomothety, if_pos hy]
      refine ⟨(hX.1 y).1.trans_le (hinc y), ?_⟩
      have := mul_pos ha (sub_pos.mpr (hX.1 y).2)
      nlinarith
    · simpa only [maskedHomothety, if_neg hy] using hX.1 y
  · intro y z hyz
    by_cases hy : U y
    · have hz := hU y z hy hyz
      simp only [maskedHomothety, if_pos hy, if_pos hz]
      have hstrict := mul_pos ha (sub_pos.mpr (hX.2 y z hyz))
      have hweak := mul_nonneg hab (sub_nonneg.mpr (hD y z hyz).2)
      nlinarith
    · by_cases hz : U z
      · simp only [maskedHomothety, if_neg hy, if_pos hz]
        exact (hX.2 y z hyz).trans_le (hinc z)
      · simpa only [maskedHomothety, if_neg hy, if_neg hz] using hX.2 y z hyz

/-- The dual lower cone on a downward closed set. -/
theorem lower_feasible (D : System ι ℝ) (hD : Normalized D)
    (U : ι → Prop) [DecidablePred U]
    (hU : ∀ y z, U z → D.edge y z = true → U y)
    {X : ι → ℝ} (hX : D.StrictlyFeasible X)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    D.StrictlyFeasible (maskedHomothety U D.lower a X) := by
  have hab : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hdec (y : ι) : a * X y + (1 - a) * D.lower y ≤ X y := by
    have := mul_nonneg hab (sub_nonneg.mpr (hX.1 y).1.le)
    nlinarith
  constructor
  · intro y
    by_cases hy : U y
    · simp only [maskedHomothety, if_pos hy]
      refine ⟨?_, (hdec y).trans_lt (hX.1 y).2⟩
      have := mul_pos ha (sub_pos.mpr (hX.1 y).1)
      nlinarith
    · simpa only [maskedHomothety, if_neg hy] using hX.1 y
  · intro y z hyz
    by_cases hz : U z
    · have hy := hU y z hz hyz
      simp only [maskedHomothety, if_pos hy, if_pos hz]
      have hstrict := mul_pos ha (sub_pos.mpr (hX.2 y z hyz))
      have hweak := mul_nonneg hab (sub_nonneg.mpr (hD y z hyz).1)
      nlinarith
    · by_cases hy : U y
      · simp only [maskedHomothety, if_pos hy, if_neg hz]
        exact (hdec y).trans_lt (hX.2 y z hyz)
      · simpa only [maskedHomothety, if_neg hy, if_neg hz] using hX.2 y z hyz

def descendantCount (D : System ι ℝ) (x : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun y : Remaining x => Reaches D x y).card

def ancestorCount (D : System ι ℝ) (x : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun y : Remaining x => Reaches D y x).card

theorem descendant_transport (D : System ι ℝ) (hD : Normalized D) (x : ι)
    (t : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ descendantCount D x * sectionVolume D x t ≤
      sectionVolume D x (a * t + (1 - a) * D.upper x) := by
  classical
  let U : ι → Prop := Reaches D x
  let T := maskedHomothety (fun y : Remaining x => U y) (fun y => D.upper y) a
  have hs : T '' sectionAt D x t ⊆ sectionAt D x (a * t + (1 - a) * D.upper x) := by
    rintro _ ⟨Y, hY, rfl⟩
    have hm := raise_feasible D hD U (fun _ _ hy hyz => hy.tail hyz) hY ha ha1
    have he : restore x (a * t + (1 - a) * D.upper x) (T Y) =
        maskedHomothety U D.upper a (restore x t Y) := by
      funext y
      by_cases hy : y = x
      · subst y
        have hx : U x := Relation.ReflTransGen.refl
        simp only [restore_self, maskedHomothety, if_pos hx]
      · simp only [restore, dif_neg hy, maskedHomothety, T]
    change D.StrictlyFeasible _
    rwa [he]
  have hm := measure_mono (μ := volume) hs
  rw [maskedHomothety_volume _ _ ha.le] at hm
  have hr := ENNReal.toReal_mono (section_volume_ne_top D x _) hm
  simpa only [descendantCount, U, sectionVolume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha.le _)] using hr

theorem ancestor_transport (D : System ι ℝ) (hD : Normalized D) (x : ι)
    (t : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ ancestorCount D x * sectionVolume D x t ≤
      sectionVolume D x (a * t + (1 - a) * D.lower x) := by
  classical
  let U : ι → Prop := fun y => Reaches D y x
  let T := maskedHomothety (fun y : Remaining x => U y) (fun y => D.lower y) a
  have hs : T '' sectionAt D x t ⊆ sectionAt D x (a * t + (1 - a) * D.lower x) := by
    rintro _ ⟨Y, hY, rfl⟩
    have hm := lower_feasible D hD U (fun _ _ hz hyz => hz.head hyz) hY ha ha1
    have he : restore x (a * t + (1 - a) * D.lower x) (T Y) =
        maskedHomothety U D.lower a (restore x t Y) := by
      funext y
      by_cases hy : y = x
      · subst y
        have hx : U x := Relation.ReflTransGen.refl
        simp only [restore_self, maskedHomothety, if_pos hx]
      · simp only [restore, dif_neg hy, maskedHomothety, T]
    change D.StrictlyFeasible _
    rwa [he]
  have hm := measure_mono (μ := volume) hs
  rw [maskedHomothety_volume _ _ ha.le] at hm
  have hr := ENNReal.toReal_mono (section_volume_ne_top D x _) hm
  simpa only [ancestorCount, U, sectionVolume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha.le _)] using hr

/-- The number of other vertices comparable with `x` in the transitive
closure, whether or not the explicit arc set is transitively closed. -/
def comparableCount (D : System ι ℝ) (x : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun y : Remaining x => Reaches D x y ∨ Reaches D y x).card

theorem descendantCount_le_comparableCount (D : System ι ℝ) (x : ι) :
    descendantCount D x ≤ comparableCount D x := by
  classical
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hy).2⟩

theorem ancestorCount_le_comparableCount (D : System ι ℝ) (x : ι) :
    ancestorCount D x ≤ comparableCount D x := by
  classical
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hy).2⟩

theorem section_towards_upper (D : System ι ℝ) (hD : Normalized D) (x : ι)
    (B : ℕ) (hB : descendantCount D x ≤ B) {t s : ℝ}
    (hts : t < s) (hs : s < D.upper x) :
    ((D.upper x - s) / (D.upper x - t)) ^ B * sectionVolume D x t ≤
      sectionVolume D x s := by
  have hden : 0 < D.upper x - t := sub_pos.mpr (hts.trans hs)
  have ha : 0 < (D.upper x - s) / (D.upper x - t) :=
    div_pos (sub_pos.mpr hs) hden
  have ha1 : (D.upper x - s) / (D.upper x - t) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have he : (D.upper x - s) / (D.upper x - t) * t +
      (1 - (D.upper x - s) / (D.upper x - t)) * D.upper x = s := by
    field_simp
    <;> ring
  have hc := descendant_transport D hD x t ha ha1
  rw [he] at hc
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ha.le ha1 hB)
    (sectionVolume_nonneg D x t)).trans hc

theorem section_towards_lower (D : System ι ℝ) (hD : Normalized D) (x : ι)
    (B : ℕ) (hB : ancestorCount D x ≤ B) {t s : ℝ}
    (hs : D.lower x < s) (hst : s < t) :
    ((s - D.lower x) / (t - D.lower x)) ^ B * sectionVolume D x t ≤
      sectionVolume D x s := by
  have hden : 0 < t - D.lower x := sub_pos.mpr (hs.trans hst)
  have ha : 0 < (s - D.lower x) / (t - D.lower x) :=
    div_pos (sub_pos.mpr hs) hden
  have ha1 : (s - D.lower x) / (t - D.lower x) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have he : (s - D.lower x) / (t - D.lower x) * t +
      (1 - (s - D.lower x) / (t - D.lower x)) * D.lower x = s := by
    field_simp
    <;> ring
  have hc := ancestor_transport D hD x t ha ha1
  rw [he] at hc
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ha.le ha1 hB)
    (sectionVolume_nonneg D x t)).trans hc

theorem middle_section_comparison (D : System ι ℝ) (hD : Normalized D)
    (x : ι) (hw : D.lower x < D.upper x) (B : ℕ)
    (hB : comparableCount D x ≤ B) {t s : ℝ}
    (ht : D.lower x < t ∧ t < D.upper x)
    (hs : D.lower x + (D.upper x - D.lower x) / 4 ≤ s ∧
      s ≤ D.upper x - (D.upper x - D.lower x) / 4) :
    (1 / 4 : ℝ) ^ B * sectionVolume D x t ≤ sectionVolume D x s := by
  have hslo : D.lower x < s := by linarith
  have hshi : s < D.upper x := by linarith
  rcases lt_trichotomy t s with hts | rfl | hst
  · have hden : 0 < D.upper x - t := sub_pos.mpr ht.2
    have hquarter : (1 / 4 : ℝ) ≤ (D.upper x - s) / (D.upper x - t) := by
      apply (le_div_iff₀ hden).mpr
      linarith
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hquarter _) (sectionVolume_nonneg D x t)).trans
      (section_towards_upper D hD x B
        ((descendantCount_le_comparableCount D x).trans hB) hts hshi)
  · exact mul_le_of_le_one_left (sectionVolume_nonneg D x t)
      (pow_le_one₀ (by norm_num) (by norm_num))
  · have hden : 0 < t - D.lower x := sub_pos.mpr ht.1
    have hquarter : (1 / 4 : ℝ) ≤ (s - D.lower x) / (t - D.lower x) := by
      apply (le_div_iff₀ hden).mpr
      linarith
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hquarter _) (sectionVolume_nonneg D x t)).trans
      (section_towards_lower D hD x B
        ((ancestorCount_le_comparableCount D x).trans hB) hslo hst)

/-- Manuscript equation `fiber-lower`, for the actual full-region marginal.
The exponent is a bound on comparable vertices, not the total graph size. -/
theorem middle_density_lower (D : System ι ℝ) (hD : Normalized D)
    (x : ι) (hw : D.lower x < D.upper x) (hV : 0 < nodeVolume D)
    (B : ℕ) (hB : comparableCount D x ≤ B) {s : ℝ}
    (hs : D.lower x + (D.upper x - D.lower x) / 4 ≤ s ∧
      s ≤ D.upper x - (D.upper x - D.lower x) / 4) :
    (1 / 4 : ℝ) ^ B / (D.upper x - D.lower x) ≤ density D x s := by
  have hi := setIntegral_mono_on
    ((sectionVolume_integrable D x).integrableOn.const_mul ((1 / 4 : ℝ) ^ B))
    (integrableOn_const (by simp : volume (Ioo (D.lower x) (D.upper x)) ≠ ⊤))
    measurableSet_Ioo (fun t ht => middle_section_comparison D hD x hw B hB ht hs)
  have hconst : (∫ _t in Ioo (D.lower x) (D.upper x), sectionVolume D x s) =
      (D.upper x - D.lower x) * sectionVolume D x s := by
    simp [(sub_pos.mpr hw).le]
  rw [integral_const_mul, integral_sectionVolume_interval, hconst] at hi
  unfold density
  apply (div_le_div_iff₀ (sub_pos.mpr hw) hV).mpr
  simpa only [mul_comm] using hi

/-- Manuscript equation `fiber-upper`, proved directly on the original
order region by integrating the ancestor and descendant cones. -/
theorem density_upper (D : System ι ℝ) (hD : Normalized D)
    (x : ι) (hw : D.lower x < D.upper x) (hV : 0 < nodeVolume D)
    (B : ℕ) (hB : comparableCount D x ≤ B) {t : ℝ}
    (ht : D.lower x < t ∧ t < D.upper x) :
    density D x t ≤ (B + 1 : ℝ) / (D.upper x - D.lower x) := by
  have hcl : Continuous (fun s : ℝ =>
      ((s - D.lower x) / (t - D.lower x)) ^ B * sectionVolume D x t) :=
    (((continuous_id.sub continuous_const).div_const _).pow _).mul_const _
  have hcu : Continuous (fun s : ℝ =>
      ((D.upper x - s) / (D.upper x - t)) ^ B * sectionVolume D x t) :=
    (((continuous_const.sub continuous_id).div_const _).pow _).mul_const _
  have hl := intervalIntegral.integral_mono_on_of_le_Ioo ht.1.le
    (hcl.intervalIntegrable _ _) (sectionVolume_integrable D x).intervalIntegrable
    (fun s hs => section_towards_lower D hD x B
      ((ancestorCount_le_comparableCount D x).trans hB) hs.1 hs.2)
  have hu := intervalIntegral.integral_mono_on_of_le_Ioo ht.2.le
    (hcu.intervalIntegrable _ _) (sectionVolume_integrable D x).intervalIntegrable
    (fun s hs => section_towards_upper D hD x B
      ((descendantCount_le_comparableCount D x).trans hB) hs.1 hs.2)
  rw [intervalIntegral.integral_mul_const, integral_lower_cone _ _ ht.1] at hl
  rw [intervalIntegral.integral_mul_const, integral_upper_cone _ _ ht.2] at hu
  have hsum := add_le_add hl hu
  rw [intervalIntegral.integral_add_adjacent_intervals
    (sectionVolume_integrable D x).intervalIntegrable
    (sectionVolume_integrable D x).intervalIntegrable,
    intervalIntegral.integral_of_le hw.le,
    integral_Ioc_eq_integral_Ioo, integral_sectionVolume_interval] at hsum
  have hm : (0 : ℝ) < B + 1 := by positivity
  have hprod : (D.upper x - D.lower x) * sectionVolume D x t ≤
      nodeVolume D * (B + 1 : ℝ) := by
    apply (div_le_iff₀ hm).mp
    calc
      _ = (t - D.lower x) / (B + 1 : ℝ) * sectionVolume D x t +
          (D.upper x - t) / (B + 1 : ℝ) * sectionVolume D x t := by ring
      _ ≤ _ := hsum
  unfold density
  apply (div_le_div_iff₀ hV (sub_pos.mpr hw)).mpr
  simpa only [mul_comm] using hprod

end

end SortingAdversary.Continuous.ComparableDensity
