import SortingAdversary.Continuous.ComparableDensity

/-!
# Fixing incomparable coordinates

The conditional regions below are actual affine coordinate sections of the
full order region. Product Lebesgue measure disintegrates along this explicit
coordinate partition. Weak endpoint assignments belong to the closure of
every nonempty conditional region.
-/

namespace SortingAdversary.Continuous.Conditioning

open FiniteAveraging OrderRegion Density ComparableDensity Set MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def join (p : ι → Prop) [DecidablePred p]
    (Z : Subtype p → ℝ) (ω : {y // ¬p y} → ℝ) : ι → ℝ :=
  fun y => if h : p y then Z ⟨y, h⟩ else ω ⟨y, h⟩

@[simp] theorem join_inside (p : ι → Prop) [DecidablePred p]
    (Z : Subtype p → ℝ) (ω : {y // ¬p y} → ℝ) (y : Subtype p) :
    join p Z ω y = Z y := by simp [join, y.property]

@[simp] theorem join_outside (p : ι → Prop) [DecidablePred p]
    (Z : Subtype p → ℝ) (ω : {y // ¬p y} → ℝ) (y : {y // ¬p y}) :
    join p Z ω y = ω y := by simp [join, y.property]

def joinEquiv (p : ι → Prop) [DecidablePred p] :
    ((Subtype p → ℝ) × ({y // ¬p y} → ℝ)) ≃ᵐ (ι → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p).symm

@[simp] theorem joinEquiv_apply (p : ι → Prop) [DecidablePred p]
    (Z : Subtype p → ℝ) (ω : {y // ¬p y} → ℝ) : joinEquiv p (Z, ω) = join p Z ω := rfl

theorem join_measurePreserving (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (joinEquiv p) volume volume :=
  MeasurePreserving.symm (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p)
    (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) p)

theorem continuous_join (p : ι → Prop) [DecidablePred p] (ω : {y // ¬p y} → ℝ) :
    Continuous (fun Z => join p Z ω) := by
  apply continuous_pi
  intro y
  by_cases hy : p y
  · simpa only [join, dif_pos hy] using (continuous_apply (⟨y, hy⟩ : Subtype p))
  · simpa only [join, dif_neg hy] using
      (continuous_const : Continuous (fun _ : Subtype p → ℝ => ω ⟨y, hy⟩))

def conditionalRegion (D : System ι ℝ) (p : ι → Prop) [DecidablePred p]
    (ω : {y // ¬p y} → ℝ) : Set (Subtype p → ℝ) :=
  (fun Z => join p Z ω) ⁻¹' region D

theorem conditionalRegion_open (D : System ι ℝ) (p : ι → Prop) [DecidablePred p]
    (ω : {y // ¬p y} → ℝ) : IsOpen (conditionalRegion D p ω) :=
  (region_open D).preimage (continuous_join p ω)

theorem join_mix (p : ι → Prop) [DecidablePred p]
    (Z T : Subtype p → ℝ) (ω : {y // ¬p y} → ℝ) (a b : ℝ) (hab : a + b = 1) :
    join p (a • Z + b • T) ω = a • join p Z ω + b • join p T ω := by
  funext y
  by_cases hy : p y
  · simp [join, hy]
  · simp only [join, dif_neg hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]

theorem conditionalRegion_convex (D : System ι ℝ) (p : ι → Prop) [DecidablePred p]
    (ω : {y // ¬p y} → ℝ) : Convex ℝ (conditionalRegion D p ω) := by
  intro Z hZ T hT a b ha hb hab
  change join p (a • Z + b • T) ω ∈ region D
  rw [join_mix p Z T ω a b hab]
  exact region_convex D hZ hT ha hb hab

theorem conditionalRegion_subset_box (D : System ι ℝ) (p : ι → Prop)
    [DecidablePred p] (ω : {y // ¬p y} → ℝ) :
    conditionalRegion D p ω ⊆ Icc (fun y : Subtype p => D.lower y)
      (fun y : Subtype p => D.upper y) := by
  intro Z hZ
  exact ⟨fun y => by simpa using (hZ.1 y).1.le,
    fun y => by simpa using (hZ.1 y).2.le⟩

theorem conditionalRegion_fubini (D : System ι ℝ) (p : ι → Prop) [DecidablePred p] :
    (∫⁻ ω, volume (conditionalRegion D p ω)) = volume (region D) := by
  have hs : MeasurableSet ((joinEquiv p) ⁻¹' region D) :=
    (region_open D).measurableSet.preimage (joinEquiv p).measurable
  have hm := (join_measurePreserving p).measure_preimage
    (region_open D).measurableSet.nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hs] at hm
  have he (ω : {y // ¬p y} → ℝ) :
      (fun Z : Subtype p → ℝ => (Z, ω)) ⁻¹' ((joinEquiv p) ⁻¹' region D) =
        conditionalRegion D p ω := by
    ext Z
    simp only [mem_preimage, joinEquiv_apply, conditionalRegion]
  simpa only [he] using hm

/-- Nonempty strict fibers have every weak endpoint assignment in their
closure; the interpolating segment fixes the frozen coordinates exactly. -/
theorem weak_mem_closure_conditionalRegion (D : System ι ℝ) (p : ι → Prop)
    [DecidablePred p] (ω : {y // ¬p y} → ℝ)
    {A Z : Subtype p → ℝ} (hA : A ∈ conditionalRegion D p ω)
    (hZ : D.WeaklyFeasible (join p Z ω)) : Z ∈ closure (conditionalRegion D p ω) := by
  let F : ℝ → (Subtype p → ℝ) := fun a => a • A + (1 - a) • Z
  have hc : Continuous F := by dsimp [F]; fun_prop
  have ht : Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 Z) := by
    simpa only [F, zero_smul, sub_zero, one_smul, zero_add] using
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)))
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a < 1 from
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num)))]
    with a ha ha1
  change D.StrictlyFeasible (join p (a • A + (1 - a) • Z) ω)
  rw [join_mix p A Z ω a (1 - a) (by ring)]
  exact strict_mix_weak D hA hZ ha (sub_nonneg.mpr ha1.le) (by ring)

def upperEndpoint (D : System ι ℝ) (z : ι) (X : ι → ℝ) : ι → ℝ := by
  classical
  exact fun y => if Reaches D z y then D.upper y else X y

def lowerEndpoint (D : System ι ℝ) (z : ι) (X : ι → ℝ) : ι → ℝ := by
  classical
  exact fun y => if Reaches D y z then D.lower y else X y

theorem upperEndpoint_weaklyFeasible (D : System ι ℝ) (hD : Normalized D)
    (z : ι) {X : ι → ℝ} (hX : D.WeaklyFeasible X) :
    D.WeaklyFeasible (upperEndpoint D z X) := by
  classical
  constructor
  · intro y
    by_cases hy : Reaches D z y
    · simp only [upperEndpoint, if_pos hy]
      exact ⟨(hX.1 y).1.trans (hX.1 y).2, le_rfl⟩
    · simpa only [upperEndpoint, if_neg hy] using hX.1 y
  · intro y w hyw
    by_cases hy : Reaches D z y
    · have hw : Reaches D z w := hy.tail hyw
      simpa only [upperEndpoint, if_pos hy, if_pos hw] using (hD y w hyw).2
    · by_cases hw : Reaches D z w
      · simpa only [upperEndpoint, if_neg hy, if_pos hw] using
          (hX.2 y w hyw).trans (hX.1 w).2
      · simpa only [upperEndpoint, if_neg hy, if_neg hw] using hX.2 y w hyw

theorem lowerEndpoint_weaklyFeasible (D : System ι ℝ) (hD : Normalized D)
    (z : ι) {X : ι → ℝ} (hX : D.WeaklyFeasible X) :
    D.WeaklyFeasible (lowerEndpoint D z X) := by
  classical
  constructor
  · intro y
    by_cases hy : Reaches D y z
    · simp only [lowerEndpoint, if_pos hy]
      exact ⟨le_rfl, (hX.1 y).1.trans (hX.1 y).2⟩
    · simpa only [lowerEndpoint, if_neg hy] using hX.1 y
  · intro y w hyw
    by_cases hw : Reaches D w z
    · have hy : Reaches D y z := hw.head hyw
      simpa only [lowerEndpoint, if_pos hy, if_pos hw] using (hD y w hyw).1
    · by_cases hy : Reaches D y z
      · simpa only [lowerEndpoint, if_pos hy, if_neg hw] using
          (hX.1 y).1.trans (hX.2 y w hyw)
      · simpa only [lowerEndpoint, if_neg hy, if_neg hw] using hX.2 y w hyw

def Related (D : System ι ℝ) (x y : ι) : Prop := Reaches D x y ∨ Reaches D y x

local instance relatedDecidable (D : System ι ℝ) (x : ι) :
    DecidablePred (Related D x) := Classical.decPred _

theorem related_self (D : System ι ℝ) (x : ι) : Related D x x :=
  Or.inl Relation.ReflTransGen.refl

theorem reaches_le {D : System ι ℝ} {X : ι → ℝ} (hX : D.WeaklyFeasible X)
    {x y : ι} (hxy : Reaches D x y) : X x ≤ X y := by
  induction hxy with
  | refl => exact le_rfl
  | @tail y z hyz he ih => exact ih.trans (hX.2 y z he)

theorem reaches_lt {D : System ι ℝ} {X : ι → ℝ} (hX : D.StrictlyFeasible X)
    {x y : ι} (hne : x ≠ y) (hxy : Reaches D x y) : X x < X y := by
  have hw : D.WeaklyFeasible X :=
    ⟨fun z => ⟨(hX.1 z).1.le, (hX.1 z).2.le⟩, fun z w hzw => (hX.2 z w hzw).le⟩
  rcases hxy.cases_tail with heq | ⟨z, hxz, hzy⟩
  · exact (hne heq.symm).elim
  · exact (reaches_le hw hxz).trans_lt (hX.2 z y hzy)

theorem upperEndpoint_outside (D : System ι ℝ) (x z : ι)
    (hxz : Reaches D x z) (X : ι → ℝ) (y : ι) (hy : ¬Related D x y) :
    upperEndpoint D z X y = X y := by
  classical
  exact if_neg (fun hzy => hy (Or.inl (hxz.trans hzy)))

theorem lowerEndpoint_outside (D : System ι ℝ) (x z : ι)
    (hzx : Reaches D z x) (X : ι → ℝ) (y : ι) (hy : ¬Related D x y) :
    lowerEndpoint D z X y = X y := by
  classical
  exact if_neg (fun hyz => hy (Or.inr (hyz.trans hzx)))

theorem join_restrict_of_outside (p : ι → Prop) [DecidablePred p]
    (ω : {y // ¬p y} → ℝ) (X : ι → ℝ) (hX : ∀ y (hy : ¬p y), X y = ω ⟨y, hy⟩) :
    join p (fun y => X y) ω = X := by
  funext y
  by_cases hy : p y
  · simp [join, hy]
  · simp only [join, dif_neg hy, hX y hy]

theorem conditional_closure_of_weak (D : System ι ℝ) (p : ι → Prop)
    [DecidablePred p] (ω : {y // ¬p y} → ℝ)
    {A : Subtype p → ℝ} (hA : A ∈ conditionalRegion D p ω)
    (X : ι → ℝ) (hX : D.WeaklyFeasible X)
    (hfixed : ∀ y (hy : ¬p y), X y = ω ⟨y, hy⟩) :
    (fun y : Subtype p => X y) ∈ closure (conditionalRegion D p ω) := by
  apply weak_mem_closure_conditionalRegion D p ω hA
  rwa [join_restrict_of_outside p ω X hfixed]

/-- Fixing all incomparable coordinates leaves the full coordinate width
visible even at the boundary of each nonempty conditional body. -/
theorem coordinate_closure_endpoints (D : System ι ℝ) (hD : Normalized D) (x : ι)
    (ω : {y // ¬Related D x y} → ℝ)
    (hC : (conditionalRegion D (Related D x) ω).Nonempty) :
    ∃ P Q : Subtype (Related D x) → ℝ,
      P ∈ closure (conditionalRegion D (Related D x) ω) ∧
      Q ∈ closure (conditionalRegion D (Related D x) ω) ∧
      P ⟨x, related_self D x⟩ = D.lower x ∧ Q ⟨x, related_self D x⟩ = D.upper x := by
  classical
  obtain ⟨A, hA⟩ := hC
  let X := join (Related D x) A ω
  have hX : D.StrictlyFeasible X := hA
  have hw : D.WeaklyFeasible X :=
    ⟨fun z => ⟨(hX.1 z).1.le, (hX.1 z).2.le⟩, fun z w hzw => (hX.2 z w hzw).le⟩
  refine ⟨fun z => lowerEndpoint D x X z, fun z => upperEndpoint D x X z, ?_, ?_, ?_, ?_⟩
  · apply conditional_closure_of_weak D (Related D x) ω hA _
      (lowerEndpoint_weaklyFeasible D hD x hw)
    intro z hz
    rw [lowerEndpoint_outside D x x Relation.ReflTransGen.refl X z hz]
    simp only [X, join, dif_neg hz]
  · apply conditional_closure_of_weak D (Related D x) ω hA _
      (upperEndpoint_weaklyFeasible D hD x hw)
    intro z hz
    rw [upperEndpoint_outside D x x Relation.ReflTransGen.refl X z hz]
    simp only [X, join, dif_neg hz]
  · simp only [lowerEndpoint, if_pos (show Reaches D x x from Relation.ReflTransGen.refl)]
  · simp only [upperEndpoint, if_pos (show Reaches D x x from Relation.ReflTransGen.refl)]

/-- For a comparable coordinate, the difference projection has width at
least the selected coordinate's original width in every nonempty fiber. -/
theorem difference_closure_endpoints (D : System ι ℝ) (hD : Normalized D)
    (x y : ι) (hne : x ≠ y) (hy : Related D x y)
    (ω : {z // ¬Related D x z} → ℝ)
    (hC : (conditionalRegion D (Related D x) ω).Nonempty) :
    ∃ P Q : Subtype (Related D x) → ℝ,
      P ∈ closure (conditionalRegion D (Related D x) ω) ∧
      Q ∈ closure (conditionalRegion D (Related D x) ω) ∧
      (Q ⟨x, related_self D x⟩ - Q ⟨y, hy⟩) -
        (P ⟨x, related_self D x⟩ - P ⟨y, hy⟩) = D.upper x - D.lower x := by
  classical
  obtain ⟨A, hA⟩ := hC
  let X := join (Related D x) A ω
  have hX : D.StrictlyFeasible X := hA
  have hw : D.WeaklyFeasible X :=
    ⟨fun z => ⟨(hX.1 z).1.le, (hX.1 z).2.le⟩, fun z w hzw => (hX.2 z w hzw).le⟩
  have hxx : Reaches D x x := Relation.ReflTransGen.refl
  have hyy : Reaches D y y := Relation.ReflTransGen.refl
  rcases hy with hxy | hyx
  · have hnot : ¬Reaches D y x := by
      intro hyx
      exact (lt_asymm (reaches_lt hX hne hxy) (reaches_lt hX hne.symm hyx))
    let P := upperEndpoint D y (lowerEndpoint D x X)
    let Q := upperEndpoint D x X
    refine ⟨fun z => P z, fun z => Q z, ?_, ?_, ?_⟩
    · apply conditional_closure_of_weak D (Related D x) ω hA _
        (upperEndpoint_weaklyFeasible D hD y (lowerEndpoint_weaklyFeasible D hD x hw))
      intro z hz
      rw [upperEndpoint_outside D x y hxy _ z hz,
        lowerEndpoint_outside D x x hxx X z hz]
      simp only [X, join, dif_neg hz]
    · apply conditional_closure_of_weak D (Related D x) ω hA _
        (upperEndpoint_weaklyFeasible D hD x hw)
      intro z hz
      rw [upperEndpoint_outside D x x hxx X z hz]
      simp only [X, join, dif_neg hz]
    · simp only [P, Q, upperEndpoint, lowerEndpoint, if_pos hxx, if_pos hyy,
        if_pos hxy, if_neg hnot]
      ring
  · have hnot : ¬Reaches D x y := by
      intro hxy
      exact (lt_asymm (reaches_lt hX hne hxy) (reaches_lt hX hne.symm hyx))
    let P := lowerEndpoint D x X
    let Q := lowerEndpoint D y (upperEndpoint D x X)
    refine ⟨fun z => P z, fun z => Q z, ?_, ?_, ?_⟩
    · apply conditional_closure_of_weak D (Related D x) ω hA _
        (lowerEndpoint_weaklyFeasible D hD x hw)
      intro z hz
      rw [lowerEndpoint_outside D x x hxx X z hz]
      simp only [X, join, dif_neg hz]
    · apply conditional_closure_of_weak D (Related D x) ω hA _
        (lowerEndpoint_weaklyFeasible D hD y (upperEndpoint_weaklyFeasible D hD x hw))
      intro z hz
      rw [lowerEndpoint_outside D x y hyx _ z hz,
        upperEndpoint_outside D x x hxx X z hz]
      simp only [X, join, dif_neg hz]
    · simp only [P, Q, upperEndpoint, lowerEndpoint, if_pos hxx, if_pos hyy,
        if_pos hyx, if_neg hnot]
      ring

end

end SortingAdversary.Continuous.Conditioning
