import SortingAdversary.Continuous.ComponentSwap

/-!
# Two-point section inequality by volume-preserving component swaps

The manuscript uses the two-point consequence of marginal log-concavity.
For these order regions it follows directly from a reversible component swap.
After shifting the second assignment, swap the two maps on the component of
the distinguished coordinate. On each of finitely many component patterns,
this is a coordinate permutation followed by a translation. Its product
Lebesgue measure is therefore unchanged.
-/

namespace SortingAdversary.Continuous.SectionConcavity

open MeasureTheory Set FiniteAveraging OrderRegion Density
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PairSpace (x : ι) := Remaining x → ℝ × ℝ

def firstAssignment (x : ι) (s : ℝ) (P : PairSpace x) : ι → ℝ :=
  restore x s (fun y => (P y).1)

def secondAssignment (x : ι) (t : ℝ) (P : PairSpace x) : ι → ℝ :=
  restore x t (fun y => (P y).2)

def shiftedAssignment (x : ι) (t δ : ℝ) (P : PairSpace x) : ι → ℝ :=
  fun y => secondAssignment x t P y - δ

def relation (D : System ι ℝ) (u v : ι) : Prop := D.edge u v = true

noncomputable def transform (D : System ι ℝ) (x : ι) (s t δ : ℝ)
    (P : PairSpace x) : PairSpace x := fun y =>
  (ComponentSwap.first (relation D) x (firstAssignment x s P) (shiftedAssignment x t δ P) y,
    ComponentSwap.second (relation D) x (firstAssignment x s P) (shiftedAssignment x t δ P) y + δ)

theorem transform_injective (D : System ι ℝ) (x : ι) (s t δ : ℝ) :
    Function.Injective (transform D x s t δ) := by
  intro P Q hpq
  have hf : ComponentSwap.first (relation D) x (firstAssignment x s P) (shiftedAssignment x t δ P) =
      ComponentSwap.first (relation D) x (firstAssignment x s Q) (shiftedAssignment x t δ Q) := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [shiftedAssignment, secondAssignment]
    · exact congrArg (fun R : PairSpace x => (R ⟨y, hy⟩).1) hpq
  have hg : ComponentSwap.second (relation D) x (firstAssignment x s P) (shiftedAssignment x t δ P) =
      ComponentSwap.second (relation D) x (firstAssignment x s Q) (shiftedAssignment x t δ Q) := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [firstAssignment]
    · have heq := congrArg (fun R : PairSpace x => (R ⟨y, hy⟩).2) hpq
      change ComponentSwap.second _ _ _ _ y + δ = ComponentSwap.second _ _ _ _ y + δ at heq
      linarith
  obtain ⟨hfirst, hsecond⟩ := ComponentSwap.recover hf hg
  funext y
  apply Prod.ext
  · have heq := congrFun hfirst y
    simpa [firstAssignment] using heq
  · have heq := congrFun hsecond y
    simp only [shiftedAssignment, secondAssignment, restore_remaining] at heq
    linarith

def sectionPair (D : System ι ℝ) (x : ι) (s t : ℝ) : Set (PairSpace x) :=
  {P | (fun y => (P y).1) ∈ sectionAt D x s ∧ (fun y => (P y).2) ∈ sectionAt D x t}

theorem transform_maps_sections (D : System ι ℝ) (x : ι) {s t δ : ℝ}
    (hδ : 0 ≤ δ) (hsep : s < t - δ) :
    MapsTo (transform D x s t δ) (sectionPair D x s t) (sectionPair D x (t - δ) (s + δ)) := by
  intro P hP
  have hf : ComponentSwap.Along (relation D) (firstAssignment x s P) := hP.1.2
  have hg : ComponentSwap.Along (relation D) (shiftedAssignment x t δ P) := by
    intro u v huv
    have h := hP.2.2 u v huv
    change secondAssignment x t P u - δ < secondAssignment x t P v - δ
    exact sub_lt_sub_right h δ
  have hroot : firstAssignment x s P x < shiftedAssignment x t δ P x := by
    simpa [firstAssignment, shiftedAssignment, secondAssignment] using hsep
  have hw := ComponentSwap.walls_swapped hf hg hroot hδ
    (L := D.lower) (U := D.upper) hP.1.1
    (by intro y; simpa [shiftedAssignment, secondAssignment] using hP.2.1 y)
  have ho := ComponentSwap.along_swapped (root := x) hf hg
  have hfirst : restore x (t - δ) (fun y => (transform D x s t δ P y).1) =
      ComponentSwap.first (relation D) x (firstAssignment x s P) (shiftedAssignment x t δ P) := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [shiftedAssignment, secondAssignment]
    · simp [restore, hy, transform]
  have hsecond : restore x (s + δ) (fun y => (transform D x s t δ P y).2) =
      (fun y => ComponentSwap.second (relation D) x
        (firstAssignment x s P) (shiftedAssignment x t δ P) y + δ) := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [firstAssignment]
    · simp [restore, hy, transform]
  constructor
  · change D.StrictlyFeasible _
    rw [hfirst]
    exact ⟨fun y => (hw y).1, ho.1⟩
  · change D.StrictlyFeasible _
    rw [hsecond]
    refine ⟨fun y => (hw y).2, ?_⟩
    intro u v huv
    have hh := ho.2 u v huv
    dsimp only
    linarith

def swapTranslate (δ : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun p => (p.2 - δ, p.1 + δ)
      invFun := fun p => (p.2 - δ, p.1 + δ)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp }
  measurable_toFun := (measurable_snd.sub_const δ).prodMk (measurable_fst.add_const δ)
  measurable_invFun := (measurable_snd.sub_const δ).prodMk (measurable_fst.add_const δ)

theorem swapTranslate_preserving (δ : ℝ) : MeasurePreserving (swapTranslate δ) volume volume := by
  have hs : MeasurePreserving Prod.swap (volume : Measure (ℝ × ℝ)) volume :=
    Measure.measurePreserving_swap
  have ht := ((measurePreserving_add_right (volume : Measure ℝ) (-δ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) δ)).comp hs
  convert ht using 1 <;> rfl

noncomputable def patch (x : ι) (δ : ℝ) (S : Finset ι) : PairSpace x ≃ᵐ PairSpace x :=
  MeasurableEquiv.piCongrRight (fun y : Remaining x =>
    if y.val ∈ S then swapTranslate δ else MeasurableEquiv.refl _)

theorem patch_preserving (x : ι) (δ : ℝ) (S : Finset ι) :
    MeasurePreserving (patch x δ S) volume volume := by
  change MeasurePreserving (fun (P : PairSpace x) (y : Remaining x) =>
    (if y.val ∈ S then swapTranslate δ else MeasurableEquiv.refl _) (P y)) volume volume
  apply volume_preserving_pi
  intro y
  by_cases hy : y.val ∈ S
  · simpa only [if_pos hy] using swapTranslate_preserving δ
  · rw [if_neg hy]
    exact MeasurePreserving.id (volume : Measure (ℝ × ℝ))

noncomputable def selected (D : System ι ℝ) (x : ι) (s t δ : ℝ) (P : PairSpace x) : Finset ι :=
  ComponentSwap.componentSet (relation D) x (firstAssignment x s P) (shiftedAssignment x t δ P)

theorem transform_eq_patch (D : System ι ℝ) (x : ι) (s t δ : ℝ) (P : PairSpace x) :
    transform D x s t δ P = patch x δ (selected D x s t δ P) P := by
  funext y
  have hmem : y.val ∈ selected D x s t δ P ↔ ComponentSwap.Component (relation D) x
      (firstAssignment x s P) (shiftedAssignment x t δ P) y := ComponentSwap.mem_componentSet ..
  by_cases hy : ComponentSwap.Component (relation D) x
      (firstAssignment x s P) (shiftedAssignment x t δ P) y
  · have hy' := hmem.mpr hy
    simp only [transform, ComponentSwap.first, ComponentSwap.second, if_pos hy]
    simp [patch, MeasurableEquiv.piCongrRight, Equiv.piCongrRight, hy', swapTranslate,
      firstAssignment, shiftedAssignment, secondAssignment]
  · have hy' : y.val ∉ selected D x s t δ P := fun h => hy (hmem.mp h)
    simp only [transform, ComponentSwap.first, ComponentSwap.second, if_neg hy]
    simp [patch, MeasurableEquiv.piCongrRight, Equiv.piCongrRight, hy',
      firstAssignment, shiftedAssignment, secondAssignment]

theorem firstAssignment_measurable (x : ι) (s : ℝ) (y : ι) :
    Measurable (fun P : PairSpace x => firstAssignment x s P y) := by
  by_cases hy : y = x
  · subst y
    simpa [firstAssignment] using (measurable_const (a := s) : Measurable (fun _ : PairSpace x => s))
  · simp only [firstAssignment, restore, dif_neg hy]
    exact measurable_fst.comp (measurable_pi_apply (⟨y, hy⟩ : Remaining x))

theorem shiftedAssignment_measurable (x : ι) (t δ : ℝ) (y : ι) :
    Measurable (fun P : PairSpace x => shiftedAssignment x t δ P y) := by
  by_cases hy : y = x
  · subst y
    simpa [shiftedAssignment, secondAssignment] using
      (measurable_const (a := t - δ) : Measurable (fun _ : PairSpace x => t - δ))
  · simpa [shiftedAssignment, secondAssignment, restore, hy] using
      ((measurable_snd.comp (measurable_pi_apply (⟨y, hy⟩ : Remaining x))).sub_const δ)

theorem selected_measurable (D : System ι ℝ) (x : ι) (s t δ : ℝ) :
    Measurable (selected D x s t δ) :=
  ComponentSwap.componentSet_measurable (relation D) x _ _
    (firstAssignment_measurable x s) (shiftedAssignment_measurable x t δ)

theorem section_measurable (D : System ι ℝ) (x : ι) (t : ℝ) :
    MeasurableSet (sectionAt D x t) := by
  have hm := (region_open D).measurableSet.preimage
    ((splitEquiv x).measurable.comp (measurable_prodMk_right (y := t)))
  convert hm using 1
  ext Y
  simp only [mem_preimage, Function.comp_apply, splitEquiv_apply, region, sectionAt, mem_ofPred_eq]

theorem sectionPair_measurable (D : System ι ℝ) (x : ι) (s t : ℝ) :
    MeasurableSet (sectionPair D x s t) :=
  ((section_measurable D x s).prod (section_measurable D x t)).preimage
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Remaining x)).measurable

theorem sectionPair_volume (D : System ι ℝ) (x : ι) (s t : ℝ) :
    volume (sectionPair D x s t) = volume (sectionAt D x s) * volume (sectionAt D x t) := by
  have hmp := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Remaining x)
  change volume ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Remaining x)) ⁻¹'
    (sectionAt D x s ×ˢ sectionAt D x t)) = _
  rw [hmp.measure_preimage ((section_measurable D x s).prod
    (section_measurable D x t)).nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod]

/-- The component map is an injection, and on each measurable component
pattern it is one of the explicitly volume-preserving maps above. -/
theorem sectionPair_volume_le (D : System ι ℝ) (x : ι) {s t δ : ℝ}
    (hδ : 0 ≤ δ) (hsep : s < t - δ) :
    volume (sectionPair D x s t) ≤ volume (sectionPair D x (t - δ) (s + δ)) := by
  classical
  let pieces (S : Finset ι) : Set (PairSpace x) :=
    sectionPair D x s t ∩ {P | selected D x s t δ P = S}
  have hp : ∀ S, MeasurableSet (pieces S) := fun S =>
    (sectionPair_measurable D x s t).inter
      (measurableSet_eq_fun (selected_measurable D x s t δ) measurable_const)
  have hcover : (⋃ S, pieces S) = sectionPair D x s t := by
    ext P
    constructor
    · intro h
      obtain ⟨S, hS⟩ := mem_iUnion.mp h
      exact hS.1
    · intro hP
      exact mem_iUnion.mpr ⟨selected D x s t δ P, hP, rfl⟩
  have heq : ∀ S P, P ∈ pieces S → transform D x s t δ P = patch x δ S P := by
    intro S P hP
    rw [transform_eq_patch, hP.2]
  have himage : ∀ S, MeasurableSet (patch x δ S '' pieces S) :=
    fun S => (patch x δ S).measurableSet_image.mpr (hp S)
  have hvol : ∀ S, volume (patch x δ S '' pieces S) = volume (pieces S) := by
    intro S
    have hm := (patch_preserving x δ S).measure_preimage (himage S).nullMeasurableSet
    rw [Set.preimage_image_eq _ (patch x δ S).injective] at hm
    exact hm.symm
  have hdisjoint : Pairwise (fun S T : Finset ι =>
      Disjoint (patch x δ S '' pieces S) (patch x δ T '' pieces T)) := by
    intro S T hst
    apply Set.disjoint_left.mpr
    rintro R ⟨P, hpP, hPR⟩ ⟨Q, hpQ, hQR⟩
    have htrans : transform D x s t δ P = transform D x s t δ Q := by
      rw [heq S P hpP, heq T Q hpQ, hPR, hQR]
    have hpq := transform_injective D x s t δ htrans
    exact hst (hpP.2.symm.trans ((congrArg (selected D x s t δ) hpq).trans hpQ.2))
  have hsub : (⋃ S, patch x δ S '' pieces S) ⊆ sectionPair D x (t - δ) (s + δ) := by
    intro R hR
    obtain ⟨S, P, hP, rfl⟩ := mem_iUnion.mp hR
    rw [← heq S P hP]
    exact transform_maps_sections D x hδ hsep hP.1
  calc
    volume (sectionPair D x s t) = volume (⋃ S, pieces S) := congrArg volume hcover.symm
    _ ≤ ∑' S, volume (pieces S) := measure_iUnion_le _
    _ = ∑' S, volume (patch x δ S '' pieces S) := tsum_congr (fun S => (hvol S).symm)
    _ = volume (⋃ S, patch x δ S '' pieces S) := (measure_iUnion hdisjoint himage).symm
    _ ≤ volume (sectionPair D x (t - δ) (s + δ)) := measure_mono hsub

/-- The exact two-point consequence of marginal log-concavity needed by the
central-interval argument, for the actual Lebesgue sections. -/
theorem sectionVolume_two_point (D : System ι ℝ) (x : ι) {s c t : ℝ}
    (hsc : s ≤ c) (hct : c ≤ t) :
    sectionVolume D x s * sectionVolume D x t ≤
      sectionVolume D x c * sectionVolume D x (s + t - c) := by
  by_cases hsame : s = c
  · subst s
    have heq : c + t - c = t := by ring
    rw [heq]
  · have hs : s < c := lt_of_le_of_ne hsc hsame
    have hm := sectionPair_volume_le D x (s := s) (t := t) (δ := t - c)
      (sub_nonneg.mpr hct) (by linarith)
    rw [sectionPair_volume, sectionPair_volume] at hm
    have hc : t - (t - c) = c := by ring
    have ht : s + (t - c) = s + t - c := by ring
    rw [hc, ht] at hm
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (section_volume_ne_top D x c)
        (section_volume_ne_top D x (s + t - c))) hm
    simpa only [sectionVolume, ENNReal.toReal_mul] using hr

/-- Normalizing the actual section volumes preserves the two-point inequality.
This theorem also covers a zero-volume region, whose defined density is zero. -/
theorem density_two_point (D : System ι ℝ) (x : ι) {s c t : ℝ}
    (hsc : s ≤ c) (hct : c ≤ t) :
    density D x s * density D x t ≤ density D x c * density D x (s + t - c) := by
  have h := div_le_div_of_nonneg_right (sectionVolume_two_point D x hsc hct)
    (mul_self_nonneg (nodeVolume D))
  simpa only [density, div_mul_div_comm] using h

end SortingAdversary.Continuous.SectionConcavity
