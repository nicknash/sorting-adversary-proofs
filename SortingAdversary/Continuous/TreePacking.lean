import SortingAdversary.Continuous.TreeSampling
import SortingAdversary.Continuous.FiniteTreeLaw
import SortingAdversary.Continuous.Dyadic
import SortingAdversary.Continuous.Packing

/-!
# Concrete packing for the continuous dyadic tree

This file discharges the sampling-mass premise. For any finite consistent tree
state, it constructs a finite common probability law from the anchors in its
paths, computes the feasible event's mass, and proves the manuscript's packing
inequality. Untouched labels can then be inserted unrestrictedly.
-/

namespace SortingAdversary.Continuous

open MeasureTheory OrderRegion
open scoped BigOperators

theorem count_of_weighted_paths {n : ℕ} {C : Type} [Fintype C]
    {k : ℝ} (hk : 1 < k) (s : TreeState.State n ℝ) (h : History n)
    (hs : s.Consistent h) (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (anchor : C ↪ ℝ) (w : C → ℝ) (hw : ∀ c, 0 ≤ w c)
    (htotal : ∑ c, w c ≤ 1 / k) (paths : Fin n → List C)
    (hlocation : ∀ i, (paths i).map anchor = s.location i) :
    (n.factorial : ℝ) * stopMass k ^ n * nodeVolume s.system *
        (∏ i, ((paths i).map w).prod) ≤ transcriptCount h := by
  classical
  let depth := Finset.univ.sup (fun i => (paths i).length)
  have hdepth : ∀ i, (paths i).length ≤ depth :=
    fun i => Finset.le_sup (f := fun i => (paths i).length) (Finset.mem_univ i)
  let nodeAt (i : Fin n) := FiniteTreeLaw.ofList depth (paths i) (hdepth i)
  let path := FiniteTreeLaw.pathEmbedding anchor depth
  let μ := FiniteTreeLaw.nodeLaw w depth
  have hone : 1 / k ≤ (1 : ℝ) := (div_le_one (by linarith : 0 < k)).mpr hk.le
  have ht := htotal.trans hone
  letI : IsProbabilityMeasure μ := FiniteTreeLaw.nodeLaw_probability w hw ht depth
  have hnode : ∀ i, path (nodeAt i) = s.location i := by
    intro i
    change (FiniteTreeLaw.path (FiniteTreeLaw.ofList depth (paths i) (hdepth i))).map anchor = _
    rw [FiniteTreeLaw.path_ofList]
    exact hlocation i
  have hcount := TreeSampling.count_of_assignedRegion s h hs hb path μ nodeAt hnode
  have hstop : stopMass k ≤ 1 - ∑ c, w c := by unfold stopMass; linarith
  have hmass : ∀ i, stopMass k * ((paths i).map w).prod ≤ μ.real {nodeAt i} := by
    intro i
    rw [FiniteTreeLaw.nodeLaw_singleton w hw ht depth (nodeAt i)]
    simpa only [nodeAt, FiniteTreeLaw.path_ofList] using
      FiniteTreeLaw.mass_lower w hw (stopMass k) hstop depth (nodeAt i)
  have hprod : stopMass k ^ n * (∏ i, ((paths i).map w).prod) ≤
      ∏ i, μ.real {nodeAt i} := by
    have hp := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => mul_nonneg (stopMass_pos hk).le
        (List.prod_nonneg (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hw c)))
      (fun i _ => hmass i)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hp
  have hz : 0 ≤ nodeVolume s.system := ENNReal.toReal_nonneg
  have hn : (0 : ℝ) ≤ n.factorial := by positivity
  calc
    (n.factorial : ℝ) * stopMass k ^ n * nodeVolume s.system *
        (∏ i, ((paths i).map w).prod) =
        n.factorial * ((stopMass k ^ n * ∏ i, ((paths i).map w).prod) *
          nodeVolume s.system) := by ring
    _ ≤ n.factorial * ((∏ i, μ.real {nodeAt i}) * nodeVolume s.system) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hz) hn
    _ ≤ transcriptCount h := hcount

/-- The product of the weights on all current item paths. -/
noncomputable def pathsWeight {n : ℕ} (k : ℝ) (paths : Fin n → List DyadicAnchor) : ℝ :=
  ∏ i, ((paths i).map (fun c => anchorWeight k c.1)).prod

@[simp] theorem pathsWeight_initial (k : ℝ) (n : ℕ) :
    pathsWeight k (fun _ : Fin n => []) = 1 := by
  simp [pathsWeight]

/-- Appending the actual refinement anchor multiplies the path product by
exactly the weight charged for that refinement. -/
theorem pathsWeight_append {n : ℕ} (k : ℝ) (paths : Fin n → List DyadicAnchor)
    (x : Fin n) (c : DyadicAnchor) :
    pathsWeight k (Function.update paths x (paths x ++ [c])) =
      pathsWeight k paths * anchorWeight k c.1 := by
  classical
  let f (i : Fin n) := ((paths i).map (fun c => anchorWeight k c.1)).prod
  have hf : (fun i => ((Function.update paths x (paths x ++ [c]) i).map
        (fun c => anchorWeight k c.1)).prod) = Function.update f x (f x * anchorWeight k c.1) := by
    funext i
    by_cases hi : i = x
    · subst i
      simp [f]
    · simp [Function.update_of_ne hi, f]
  unfold pathsWeight
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ x), Fintype.prod_eq_mul_prod_compl x f]
  simp only [Finset.compl_eq_univ_sdiff]
  ring

theorem pathsWeight_pos {n : ℕ} {k : ℝ} (hk : 1 < k) (paths : Fin n → List DyadicAnchor) :
    0 < pathsWeight k paths := by
  apply Finset.prod_pos
  intro i hi
  apply List.prod_pos
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact anchorWeight_pos hk c.1

/-- The full packing inequality for actual dyadic paths. The finite sampling
alphabet and its normalized probability law are constructed in the proof. -/
theorem dyadic_tree_packing {n : ℕ} {k : ℝ} (hk : 1 < k)
    (s : TreeState.State n ℝ) (h : History n) (hs : s.Consistent h)
    (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (paths : Fin n → List DyadicAnchor)
    (hlocation : ∀ i, (paths i).map (fun c => (c.coordinate : ℝ)) = s.location i) :
    (n.factorial : ℝ) * stopMass k ^ n * nodeVolume s.system * pathsWeight k paths ≤
      transcriptCount h := by
  classical
  let used : Finset DyadicAnchor := Finset.univ.biUnion (fun i => (paths i).toFinset)
  have hmem : ∀ i c, c ∈ paths i → c ∈ used := by
    intro i c hc
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr hc⟩
  let coded (i : Fin n) : List used := (paths i).attachWith (fun c => c ∈ used) (hmem i)
  let anchor : used ↪ ℝ :=
    ⟨fun c => (c.val.coordinate : ℝ), by
      intro c d heq
      apply Subtype.ext
      apply DyadicAnchor.coordinate_injective
      change (c.val.coordinate : ℝ) = (d.val.coordinate : ℝ) at heq
      exact_mod_cast heq⟩
  let w (c : used) := anchorWeight k c.val.1
  have hw : ∀ c, 0 ≤ w c := fun c => (anchorWeight_pos hk c.val.1).le
  have ht : ∑ c, w c ≤ 1 / k := by
    have heq : (∑ c : used, w c) = ∑ c ∈ used, anchorWeight k c.1 :=
      Finset.sum_coe_sort used (fun c => anchorWeight k c.1)
    rw [heq]
    exact child_mass_le hk used
  have hl : ∀ i, (coded i).map anchor = s.location i := by
    intro i
    change ((paths i).attachWith (fun c => c ∈ used) (hmem i)).map
      (fun c => (c.val.coordinate : ℝ)) = s.location i
    exact (List.attachWith_map_val (f := fun c => (c.coordinate : ℝ)) (hmem i)).trans
      (hlocation i)
  have hc := count_of_weighted_paths hk s h hs hb anchor w hw ht coded hl
  have hwmap : ∀ i, (coded i).map w = (paths i).map (fun c => anchorWeight k c.1) := by
    intro i
    exact List.attachWith_map_val (f := fun c => anchorWeight k c.1) (hmem i)
  simp_rw [hwmap] at hc
  exact hc

/-- Unqueried labels contribute all unrestricted insertion positions, so the
ambient factorial survives sampling only the queried labels. -/
theorem dyadic_tree_packing_with_untouched {n : ℕ} {k : ℝ} (hk : 1 < k)
    (s : TreeState.State n ℝ) (h : History n) (hs : s.Consistent h)
    (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (paths : Fin n → List DyadicAnchor)
    (hlocation : ∀ i, (paths i).map (fun c => (c.coordinate : ℝ)) = s.location i)
    (r : ℕ) (embedding : Item n ↪ Item (n + r)) :
    ((n + r).factorial : ℝ) * stopMass k ^ n * nodeVolume s.system * pathsWeight k paths ≤
      transcriptCount (mapHistory embedding h) := by
  have hsmall := dyadic_tree_packing hk s h hs hb paths hlocation
  have hfree : ((n + r).factorial : ℝ) * transcriptCount h ≤
      n.factorial * (transcriptCount (mapHistory embedding h) : ℝ) := by
    exact_mod_cast embedded_history_count h r embedding
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hlarge := mul_le_mul_of_nonneg_left hsmall
    (by positivity : (0 : ℝ) ≤ (n + r).factorial)
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

/-- The final prefix bound now uses concrete tree consistency and volume.
The remaining log equality and event/arc conditions are the controller's
bookkeeping invariants, not a probabilistic packing assumption. -/
theorem prefix_count_of_dyadic_tree {k n : ℕ} (hk : 64 ≤ k)
    (s : TreeState.State n ℝ) (h : History n) (hs : s.Consistent h)
    (hb : ∀ i, 0 ≤ s.system.lower i ∧ s.system.upper i ≤ 1)
    (paths : Fin n → List DyadicAnchor)
    (hlocation : ∀ i, (paths i).map (fun c => (c.coordinate : ℝ)) = s.location i)
    (r : ℕ) (embedding : Item n ↪ Item (n + r)) (L : AccountingLog)
    (hZ : 0 < nodeVolume s.system)
    (hweight : pathsWeight k paths = L.weightProduct k)
    (hvolume : log2 (nodeVolume s.system) = L.logVolume) (hvolume_le : L.logVolume ≤ 0)
    (he : ∀ e ∈ L.events, e.Valid k)
    (hloss : ∀ a ∈ L.losses, a ≤ answerLoss k)
    (harcs : k * L.degreeRepairs ≤ L.comparisons)
    (hqueried : n ≤ 2 * L.comparisons) (hlength : L.comparisons = h.length) :
    log2 ((n + r).factorial : ℝ) - (1 + prefixOverhead k) * h.length ≤
      log2 (transcriptCount (mapHistory embedding h) : ℝ) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hcount := dyadic_tree_packing_with_untouched hk1 s h hs hb paths hlocation r embedding
  rw [hweight] at hcount
  have hpacking := log_packing hk1 hZ L hcount
  rw [hvolume] at hpacking
  have hp := prefix_bound_of_packing hk L n _ _ he hloss hvolume_le harcs hqueried hpacking
  simpa only [hlength] using hp

end SortingAdversary.Continuous
