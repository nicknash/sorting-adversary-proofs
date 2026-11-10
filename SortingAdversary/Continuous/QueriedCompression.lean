import SortingAdversary.Continuous.TreePacking
import SortingAdversary.Continuous.TreeVolume
import SortingAdversary.Continuous.Conditioning

/-!
# Removing the untouched unit coordinates for counting

The executable state may retain all `n` labels. Outside the queried set the
coordinates are still isolated unit intervals, and the paths are empty.
Those coordinates contribute volume one and path weight one. Compressing to
the queried labels therefore preserves both geometric quantities while making
the stopping penalty depend on the number of queried labels.
-/

namespace SortingAdversary.Continuous.QueriedCompression

open MeasureTheory Set FiniteAveraging OrderRegion TreeState
open scoped BigOperators

def pullback {α β : Type*} (D : System β ℝ) (f : α → β) : System α ℝ where
  lower x := D.lower (f x)
  upper x := D.upper (f x)
  edge x y := D.edge (f x) (f y)

theorem pullback_region {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (D : System β ℝ) (e : α ≃ β) :
    region (pullback D e) =
      (MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e) ⁻¹' region D := by
  ext Y
  constructor
  · intro hY
    constructor
    · intro y
      simpa [pullback, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using hY.1 (e.symm y)
    · intro y z hyz
      have h := hY.2 (e.symm y) (e.symm z) (by simpa [pullback] using hyz)
      simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using h
  · intro hY
    constructor
    · intro y
      simpa [pullback, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using hY.1 (e y)
    · intro y z hyz
      have h := hY.2 (e y) (e z) hyz
      simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using h

theorem pullback_volume {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (D : System β ℝ) (e : α ≃ β) :
    nodeVolume (pullback D e) = nodeVolume D := by
  unfold nodeVolume
  rw [pullback_region, (volume_measurePreserving_piCongrLeft (fun _ : β => ℝ) e).measure_preimage
    (region_open D).measurableSet.nullMeasurableSet]

variable {n : ℕ}

def activeSystem (D : System (Fin n) ℝ) (A : Finset (Fin n)) : System A ℝ :=
  pullback D Subtype.val

theorem joined_feasible_iff (D : System (Fin n) ℝ) (A : Finset (Fin n))
    (hunit : ∀ x ∉ A, IsolatedUnit D x) (Z : A → ℝ) (ω : {x // x ∉ A} → ℝ) :
    D.StrictlyFeasible (Conditioning.join (fun x => x ∈ A) Z ω) ↔
      (activeSystem D A).StrictlyFeasible Z ∧ ∀ x, 0 < ω x ∧ ω x < 1 := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x
      simpa [activeSystem, pullback] using h.1 x
    · intro x y hxy
      simpa using h.2 x y hxy
    · intro x
      have hx := hunit x x.property
      simpa [hx.1, hx.2.1] using h.1 x
  · rintro ⟨hZ, hω⟩
    constructor
    · intro x
      by_cases hx : x ∈ A
      · simpa [Conditioning.join, hx, activeSystem, pullback] using hZ.1 ⟨x, hx⟩
      · have hu := hunit x hx
        simpa [Conditioning.join, hx, hu.1, hu.2.1] using hω ⟨x, hx⟩
    · intro x y hxy
      have hx : x ∈ A := by
        by_contra hx
        have he := (hunit x hx).2.2 y
        simp [he.1] at hxy
      have hy : y ∈ A := by
        by_contra hy
        have he := (hunit y hy).2.2 x
        simp [he.2] at hxy
      simpa [Conditioning.join, hx, hy] using hZ.2 ⟨x, hx⟩ ⟨y, hy⟩ hxy

/-- The complement contributes a Cartesian product of unit intervals. -/
theorem activeSystem_volume (D : System (Fin n) ℝ) (A : Finset (Fin n))
    (hunit : ∀ x ∉ A, IsolatedUnit D x) : nodeVolume (activeSystem D A) = nodeVolume D := by
  let p : Fin n → Prop := fun x => x ∈ A
  have hset : (Conditioning.joinEquiv p) ⁻¹' region D =
      region (activeSystem D A) ×ˢ Set.univ.pi (fun _ : {x // x ∉ A} => Ioo (0 : ℝ) 1) := by
    ext X
    exact (joined_feasible_iff D A hunit X.1 X.2).trans
      (by simp only [mem_prod, mem_univ_pi, mem_Ioo]; rfl)
  have hm := (Conditioning.join_measurePreserving p).measure_preimage
    (region_open D).measurableSet.nullMeasurableSet
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod] at hm
  have hcube : volume (Set.univ.pi (fun _ : {x // x ∉ A} => Ioo (0 : ℝ) 1)) = 1 := by
    change (Measure.pi (fun _ : {x : Fin n // x ∉ A} => (volume : Measure ℝ)))
      (Set.univ.pi (fun _ => Ioo (0 : ℝ) 1)) = 1
    rw [Measure.pi_pi]
    simp
  rw [hcube, mul_one] at hm
  have hfi : (Subtype.fintype p) = Finset.Subtype.fintype A := Subsingleton.elim _ _
  rw [hfi] at hm
  exact congrArg ENNReal.toReal hm

noncomputable def embedding (A : Finset (Fin n)) : Fin A.card ↪ Fin n :=
  A.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype fun x => x ∈ A)

@[simp] theorem embedding_mem (A : Finset (Fin n)) (x : Fin A.card) : embedding A x ∈ A :=
  (A.equivFin.symm x).property

theorem range_embedding (A : Finset (Fin n)) : Set.range (embedding A) = A := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact embedding_mem A y
  · intro hx
    refine ⟨A.equivFin ⟨x, hx⟩, ?_⟩
    simp [embedding]

noncomputable def compress (s : State n ℝ) (A : Finset (Fin n)) : State A.card ℝ where
  system := pullback s.system (embedding A)
  location i := s.location (embedding A i)

theorem compress_volume (s : State n ℝ) (A : Finset (Fin n))
    (hunit : ∀ x ∉ A, IsolatedUnit s.system x) :
    nodeVolume (compress s A).system = nodeVolume s.system := by
  have heq : (compress s A).system = pullback (activeSystem s.system A) A.equivFin.symm := rfl
  rw [heq, pullback_volume, activeSystem_volume s.system A hunit]

noncomputable def extend (A : Finset (Fin n)) (Z : Fin A.card → ℝ) : Fin n → ℝ :=
  Conditioning.join (fun x => x ∈ A) (fun x => Z (A.equivFin x)) (fun _ => 1 / 2)

@[simp] theorem extend_embedding (A : Finset (Fin n)) (Z : Fin A.card → ℝ) (i : Fin A.card) :
    extend A Z (embedding A i) = Z i := by
  simp [extend, embedding, Conditioning.join]

theorem extend_feasible (s : State n ℝ) (A : Finset (Fin n))
    (hunit : ∀ x ∉ A, IsolatedUnit s.system x) (Z : Fin A.card → ℝ)
    (hZ : (compress s A).system.StrictlyFeasible Z) : s.system.StrictlyFeasible (extend A Z) := by
  apply (joined_feasible_iff s.system A hunit _ _).mpr
  refine ⟨⟨?_, ?_⟩, by intro x; norm_num⟩
  · intro x
    simpa [compress, pullback, embedding, activeSystem] using hZ.1 (A.equivFin x)
  · intro x y hxy
    have hxy' : (compress s A).system.edge (A.equivFin x) (A.equivFin y) = true := by
      simpa [compress, pullback, embedding, activeSystem] using hxy
    exact hZ.2 _ _ hxy'

theorem compress_consistent (s : State n ℝ) (A : Finset (Fin n)) (h : History A.card)
    (hs : s.Consistent (mapHistory (embedding A) h))
    (hunit : ∀ x ∉ A, IsolatedUnit s.system x) : (compress s A).Consistent h := by
  intro Z hZ o ho
  have hold := hs (extend A Z) (extend_feasible s A hunit Z hZ) (mapObservation (embedding A) o)
    (List.mem_map.mpr ⟨o, ho, rfl⟩)
  cases ha : o.answer <;>
    simpa [State.Holds, State.position, mapObservation, mapQuery, compress, ha] using hold

theorem compress_pathsWeight (k : ℝ) (paths : Fin n → List DyadicAnchor) (A : Finset (Fin n))
    (hempty : ∀ x ∉ A, paths x = []) :
    pathsWeight k (fun i => paths (embedding A i)) = pathsWeight k paths := by
  classical
  let f (x : Fin n) := ((paths x).map (fun c => anchorWeight k c.1)).prod
  have heq : (∏ i : Fin A.card, f (embedding A i)) = ∏ x : A, f x :=
    A.equivFin.symm.prod_comp (fun x : A => f x)
  change (∏ i : Fin A.card, f (embedding A i)) = ∏ x, f x
  rw [heq, Finset.prod_coe_sort]
  exact Finset.prod_subset (f := f) A.subset_univ (fun x hx hxA => by simp [f, hempty x hxA])

/-- A full state may be sampled on any supported active set, provided every
other coordinate is still an untouched isolated unit coordinate. -/
theorem packing_on_active {k : ℝ} (hk : 1 < k) (s : State n ℝ) (h : History n)
    (hs : s.Consistent h) (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (paths : Fin n → List DyadicAnchor)
    (hlocation : ∀ i, (paths i).map (fun c => (c.coordinate : ℝ)) = s.location i)
    (A : Finset (Fin n)) (hunit : ∀ x ∉ A, IsolatedUnit s.system x)
    (hempty : ∀ x ∉ A, paths x = [])
    (hsupport : ∀ o ∈ h, o.query.left ∈ A ∧ o.query.right ∈ A) :
    (n.factorial : ℝ) * stopMass k ^ A.card * nodeVolume s.system * pathsWeight k paths ≤
      transcriptCount h := by
  obtain ⟨h', hh'⟩ := exists_compressed_history (embedding A) h (by
    intro o ho
    rw [range_embedding]
    exact hsupport o ho)
  have hc : (compress s A).Consistent h' :=
    compress_consistent s A h' (by simpa only [hh'] using hs) hunit
  have hb' : ∀ i, 0 ≤ (compress s A).system.lower i ∧ (compress s A).system.upper i ≤ 1 :=
    fun i => hb (embedding A i)
  have hl' : ∀ i, (paths (embedding A i)).map (fun c => (c.coordinate : ℝ)) =
      (compress s A).location i := fun i => hlocation (embedding A i)
  have hsmall := dyadic_tree_packing hk (compress s A) h' hc hb'
    (fun i => paths (embedding A i)) hl'
  rw [compress_volume s A hunit, compress_pathsWeight k paths A hempty] at hsmall
  have hfree : (n.factorial : ℝ) * transcriptCount h' ≤
      A.card.factorial * (transcriptCount h : ℝ) := by
    have hf := embedded_history_count_general h' (embedding A)
    rw [hh'] at hf
    exact_mod_cast hf
  have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ n.factorial)
  have hspos : (0 : ℝ) < A.card.factorial := by positivity
  apply (mul_le_mul_iff_right₀ hspos).mp
  nlinarith

/-- The paper's packing inequality for a full `n`-label controller state.
Only labels actually mentioned in the transcript pay a stopping factor. -/
theorem packing_queried {k : ℝ} (hk : 1 < k) (s : State n ℝ) (h : History n)
    (hs : s.Consistent h) (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (paths : Fin n → List DyadicAnchor)
    (hlocation : ∀ i, (paths i).map (fun c => (c.coordinate : ℝ)) = s.location i)
    (hunit : ∀ x ∉ queriedLabels h, IsolatedUnit s.system x)
    (hempty : ∀ x ∉ queriedLabels h, paths x = []) :
    (n.factorial : ℝ) * stopMass k ^ (queriedLabels h).card *
        nodeVolume s.system * pathsWeight k paths ≤ transcriptCount h :=
  packing_on_active hk s h hs hb paths hlocation (queriedLabels h) hunit hempty
    (queriedLabels_members h)

/-- Prefix counting for a full controller state, with both the probability
calculation and queried-label compression discharged. -/
theorem prefix_count {k : ℕ} (hk : 64 ≤ k) (s : State n ℝ) (h : History n)
    (hs : s.Consistent h) (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (paths : Fin n → List DyadicAnchor)
    (hlocation : ∀ i, (paths i).map (fun c => (c.coordinate : ℝ)) = s.location i)
    (hunit : ∀ x ∉ queriedLabels h, IsolatedUnit s.system x)
    (hempty : ∀ x ∉ queriedLabels h, paths x = [])
    (L : AccountingLog) (hZ : 0 < nodeVolume s.system)
    (hweight : pathsWeight k paths = L.weightProduct k)
    (hvolume : log2 (nodeVolume s.system) = L.logVolume)
    (he : ∀ e ∈ L.events, e.Valid k) (hloss : ∀ a ∈ L.losses, a ≤ answerLoss k)
    (harcs : k * L.degreeRepairs ≤ L.comparisons) (hlength : L.comparisons = h.length) :
    log2 (n.factorial : ℝ) - (1 + prefixOverhead k) * h.length ≤
      log2 (transcriptCount h : ℝ) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hcount := packing_queried hk1 s h hs hb paths hlocation hunit hempty
  rw [hweight] at hcount
  have hp := log_packing hk1 hZ L hcount
  rw [hvolume] at hp
  have hv : L.logVolume ≤ 0 := by
    rw [← hvolume]
    exact log2_nonpos hZ (nodeVolume_le_one s.system (fun i => (hb i).1) (fun i => (hb i).2))
  have hq : (queriedLabels h).card ≤ 2 * L.comparisons := by
    rw [hlength]
    exact queriedLabels_card_le h
  have hfinal := prefix_bound_of_packing hk L (queriedLabels h).card _ _
    he hloss hv harcs hq hp
  simpa only [hlength] using hfinal

end SortingAdversary.Continuous.QueriedCompression
