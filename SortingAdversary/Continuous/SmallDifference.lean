import SortingAdversary.Continuous.Conditioning
import SortingAdversary.Continuous.ProjectionDensity
import SortingAdversary.Continuous.RegionMeasure

/-!
# Anti-concentration of actual coordinate differences

Condition on all vertices incomparable with the selected vertex. The remaining
body has at most `B+1` coordinates and retains a difference projection of width
at least the selected coordinate's canonical width. The convex projection
bound is uniform in the frozen coordinates, so Fubini gives the full-region
probability bound used by the finite certificates.
-/

namespace SortingAdversary.Continuous.SmallDifference

open FiniteAveraging OrderRegion ComparableDensity Conditioning Set MeasureTheory
open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance relatedDecidable (D : System ι ℝ) (x : ι) :
    DecidablePred (Related D x) := Classical.decPred _

theorem remaining_card_add_one (x : ι) : Fintype.card (Remaining x) + 1 = Fintype.card ι := by
  simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe x)

theorem related_card (D : System ι ℝ) (x : ι) :
    Fintype.card (Subtype (Related D x)) = comparableCount D x + 1 := by
  classical
  let x' : Subtype (Related D x) := ⟨x, related_self D x⟩
  let e : Remaining x' ≃ {y : Remaining x // Related D x y} :=
    { toFun := fun z => ⟨⟨z.val.val, fun h => z.property (Subtype.ext h)⟩, z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val, z.property⟩,
        fun h => z.val.property (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : Fintype.card (Remaining x') = comparableCount D x := by
    rw [Fintype.card_congr e]
    unfold comparableCount
    exact Fintype.card_of_subtype _ (fun y => by simp [Related])
  rw [← remaining_card_add_one x', he]

theorem fubini_partition (p : ι → Prop) [DecidablePred p]
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    (∫⁻ ω : {y // ¬p y} → ℝ, volume ((fun Z : Subtype p → ℝ => join p Z ω) ⁻¹' E)) =
      volume E := by
  have hs : MeasurableSet ((joinEquiv p) ⁻¹' E) := hE.preimage (joinEquiv p).measurable
  have hm := (join_measurePreserving p).measure_preimage hE.nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hs] at hm
  have he (ω : {y // ¬p y} → ℝ) :
      (fun Z : Subtype p → ℝ => (Z, ω)) ⁻¹' ((joinEquiv p) ⁻¹' E) =
        (fun Z => join p Z ω) ⁻¹' E := by
    ext Z
    simp only [mem_preimage, joinEquiv_apply]
  simpa only [he] using hm

private theorem coefficient_mono (D : System ι ℝ) (x : ι) (B : ℕ)
    (hB : comparableCount D x ≤ B) {a b : ℝ} (hab : a ≤ b)
    (hw : D.lower x < D.upper x) (V : ℝ) (hV : 0 ≤ V) :
    (Fintype.card (Remaining (⟨x, related_self D x⟩ : Subtype (Related D x))) + 1 : ℝ) *
        (b - a) / (D.upper x - D.lower x) * V ≤
      (B + 1 : ℝ) * (b - a) / (D.upper x - D.lower x) * V := by
  have hd : (Fintype.card (Remaining (⟨x, related_self D x⟩ : Subtype (Related D x))) + 1 : ℝ) ≤
      (B + 1 : ℝ) := by
    exact_mod_cast (show Fintype.card (Remaining (⟨x, related_self D x⟩ : Subtype (Related D x))) + 1 ≤
        B + 1 by rw [remaining_card_add_one, related_card]; omega)
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hab))
      (sub_nonneg.mpr hw.le)) hV

private theorem conditional_fixed_bound (D : System ι ℝ) (hD : Normalized D)
    (x : ι) (B : ℕ) (hB : comparableCount D x ≤ B) (hw : D.lower x < D.upper x)
    (ω : {y // ¬Related D x y} → ℝ) (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (volume (conditionalRegion D (Related D x) ω ∩
      {Z | join (Related D x) Z ω x - c ∈ Icc a b})).toReal ≤
        (B + 1 : ℝ) * (b - a) / (D.upper x - D.lower x) *
          (volume (conditionalRegion D (Related D x) ω)).toReal := by
  let C := conditionalRegion D (Related D x) ω
  let x' : Subtype (Related D x) := ⟨x, related_self D x⟩
  by_cases hC : C.Nonempty
  · obtain ⟨P, Q, hP, hQ, hPl, hQu⟩ := coordinate_closure_endpoints D hD x ω hC
    have hpq : P x' < Q x' := by simpa only [x', hPl, hQu] using hw
    have hh := ProjectionDensity.band_volume_le
      (conditionalRegion_open D (Related D x) ω)
      (conditionalRegion_convex D (Related D x) ω)
      (conditionalRegion_subset_box D (Related D x) ω) x' hP hQ hpq
      (show a + c ≤ b + c by linarith)
    have he : C ∩ {Z | join (Related D x) Z ω x - c ∈ Icc a b} =
        C ∩ {Z | Z x' ∈ Icc (a + c) (b + c)} := by
      ext Z
      have hx : join (Related D x) Z ω x = Z x' := join_inside _ _ _ x'
      simp only [mem_inter_iff, mem_setOf_eq, hx, mem_Icc]
      constructor <;> rintro ⟨hz, h₁, h₂⟩ <;> exact ⟨hz, by linarith, by linarith⟩
    rw [he]
    have hwidth : Q x' - P x' = D.upper x - D.lower x := by rw [hQu, hPl]
    rw [hwidth, add_sub_add_right_eq_sub] at hh
    exact hh.trans (coefficient_mono D x B hB hab hw _ ENNReal.toReal_nonneg)
  · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hC
    simp only [C] at he
    simp [he]

private theorem conditional_difference_bound (D : System ι ℝ) (hD : Normalized D)
    (x y : ι) (hne : x ≠ y) (B : ℕ) (hB : comparableCount D x ≤ B)
    (hw : D.lower x < D.upper x) (ω : {z // ¬Related D x z} → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    (volume (conditionalRegion D (Related D x) ω ∩
      {Z | join (Related D x) Z ω x - join (Related D x) Z ω y ∈ Icc a b})).toReal ≤
        (B + 1 : ℝ) * (b - a) / (D.upper x - D.lower x) *
          (volume (conditionalRegion D (Related D x) ω)).toReal := by
  let C := conditionalRegion D (Related D x) ω
  by_cases hy : Related D x y
  · let x' : Subtype (Related D x) := ⟨x, related_self D x⟩
    let y' : Subtype (Related D x) := ⟨y, hy⟩
    have hne' : x' ≠ y' := fun heq => hne (congrArg Subtype.val heq)
    by_cases hC : C.Nonempty
    · obtain ⟨P, Q, hP, hQ, hwidth⟩ := difference_closure_endpoints D hD x y hne hy ω hC
      have hpq : P x' - P y' < Q x' - Q y' := by
        have hW : 0 < D.upper x - D.lower x := sub_pos.mpr hw
        change (Q x' - Q y') - (P x' - P y') = _ at hwidth
        linarith
      have hh := ProjectionDensity.difference_band_volume_le
        (conditionalRegion_open D (Related D x) ω)
        (conditionalRegion_convex D (Related D x) ω)
        (conditionalRegion_subset_box D (Related D x) ω) x' y' hne' hP hQ hpq hab
      have hx (Z) : join (Related D x) Z ω x = Z x' := join_inside _ _ _ x'
      have hy' (Z) : join (Related D x) Z ω y = Z y' := join_inside _ _ _ y'
      simp_rw [hx, hy']
      rw [hwidth] at hh
      exact hh.trans (coefficient_mono D x B hB hab hw _ ENNReal.toReal_nonneg)
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hC
      simp only [C] at he
      simp [he]
  · have hy' (Z) : join (Related D x) Z ω y = ω ⟨y, hy⟩ := join_outside _ _ _ ⟨y, hy⟩
    simp_rw [hy']
    exact conditional_fixed_bound D hD x B hB hw ω (ω ⟨y, hy⟩) hab

/-- Integrate a uniform conditional bound through the explicit coordinate
partition. This helper uses genuine conditional volumes, not probability
values supplied by an oracle. -/
theorem uniform_event_le_of_conditional_bound (D : System ι ℝ)
    (p : ι → Prop) [DecidablePred p] (E : Set (ι → ℝ)) (hE : MeasurableSet E)
    (c : ℝ) (hc : 0 ≤ c) (hV : 0 < nodeVolume D)
    (hbound : ∀ ω : {y // ¬p y} → ℝ,
      (volume (conditionalRegion D p ω ∩ {Z | join p Z ω ∈ E})).toReal ≤
        c * (volume (conditionalRegion D p ω)).toReal) :
    (uniformMeasure D).real E ≤ c := by
  have hslice (ω : {y // ¬p y} → ℝ) :
      volume ((fun Z : Subtype p → ℝ => join p Z ω) ⁻¹' (region D ∩ E)) ≤
        ENNReal.ofReal c * volume (conditionalRegion D p ω) := by
    have he : (fun Z : Subtype p → ℝ => join p Z ω) ⁻¹' (region D ∩ E) =
        conditionalRegion D p ω ∩ {Z | join p Z ω ∈ E} := rfl
    have hfinite := ProjectionDensity.volume_ne_top (conditionalRegion_subset_box D p ω)
    have hefinite := ne_top_of_le_ne_top hfinite
      (measure_mono (μ := volume) (inter_subset_left :
        conditionalRegion D p ω ∩ {Z | join p Z ω ∈ E} ⊆ conditionalRegion D p ω))
    rw [he]
    apply (ENNReal.toReal_le_toReal hefinite
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hbound ω
  have hi := lintegral_mono (μ := volume) hslice
  rw [fubini_partition p (region D ∩ E) ((region_open D).measurableSet.inter hE),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, conditionalRegion_fubini] at hi
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (OrderRegion.volume_ne_top D)) hi
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hreal
  rw [uniformMeasure_real D E hE]
  apply (div_le_iff₀ hV).mpr
  simpa only [inter_comm, nodeVolume] using hreal

/-- Manuscript `gap`, with a fixed real threshold. Closed intervals include
all endpoint cases needed by the finite probability certificates. -/
theorem fixed_probability_le (D : System ι ℝ) (hD : Normalized D)
    (x : ι) (B : ℕ) (hB : comparableCount D x ≤ B)
    (hw : D.lower x < D.upper x) (hV : 0 < nodeVolume D)
    (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (uniformMeasure D).real {X | X x - c ∈ Icc a b} ≤
      (B + 1 : ℝ) * (b - a) / (D.upper x - D.lower x) := by
  apply uniform_event_le_of_conditional_bound D (Related D x) _
    (measurableSet_Icc.preimage ((measurable_pi_apply x).sub_const c)) _
    (by positivity) hV
  intro ω
  exact conditional_fixed_bound D hD x B hB hw ω c hab

/-- Manuscript `gap`, for the difference of any two distinct coordinates.
The proof covers comparable and incomparable pairs separately inside the
conditional fibers, then integrates the same bound over the frozen values. -/
theorem difference_probability_le (D : System ι ℝ) (hD : Normalized D)
    (x y : ι) (hne : x ≠ y) (B : ℕ) (hB : comparableCount D x ≤ B)
    (hw : D.lower x < D.upper x) (hV : 0 < nodeVolume D)
    {a b : ℝ} (hab : a ≤ b) :
    (uniformMeasure D).real {X | X x - X y ∈ Icc a b} ≤
      (B + 1 : ℝ) * (b - a) / (D.upper x - D.lower x) := by
  apply uniform_event_le_of_conditional_bound D (Related D x) _
    (measurableSet_Icc.preimage ((measurable_pi_apply x).sub (measurable_pi_apply y))) _
    (by positivity) hV
  intro ω
  exact conditional_difference_bound D hD x y hne B hB hw ω hab

end

end SortingAdversary.Continuous.SmallDifference
