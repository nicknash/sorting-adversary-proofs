import SortingAdversary.Continuous.ArbitraryLabels
import SortingAdversary.Continuous.DensityCertificates
import SortingAdversary.Continuous.RationalState

/-!
# Probability and gain specifications for the original-label routines

Reindexing preserves the actual uniform feasible-region measure. These
theorems interpret the executable public routines in the original coordinate
system, including their dyadic refinement and anchor outputs.
-/

namespace SortingAdversary.Continuous.ArbitraryLabels

open FiniteAveraging OrderRegion GraphOrder Certificates EnclosureParameters
open Density MeasureTheory Set

variable {n : ℕ}

theorem normalize_toReal (D : System (Fin n) ℚ) :
    (normalize D).toReal = OrderRegion.normalize D.toReal (rankOrder (graphRank D)) :=
  TreeState.normalizeSystem_toReal D _

theorem normalize_region (D : System (Fin n) ℚ) : region (normalize D).toReal = region D.toReal := by
  rw [normalize_toReal, OrderRegion.normalize_region]

theorem comparison_probability_reindex (D : System (Fin n) ℚ) (x y : Fin n) (a : Answer) :
    (uniformMeasure (indexed D).toReal).real (LocalSelection.comparisonEvent (index D x) (index D y) a) =
      (uniformMeasure D.toReal).real (LocalSelection.comparisonEvent x y a) := by
  have hpre : assignmentEquiv (orderEquiv D) ⁻¹' LocalSelection.comparisonEvent x y a =
      LocalSelection.comparisonEvent (index D x) (index D y) a := by
    cases a <;> ext X <;> simp only [LocalSelection.comparisonEvent, mem_preimage,
      mem_ofPred_eq, assignmentEquiv_apply, index]
  change (uniformMeasure (D.toReal.reindex (orderEquiv D))).real _ = _
  rw [← hpre]
  exact uniformMeasure_reindex_real D.toReal (orderEquiv D) _
    (LocalSelection.comparisonEvent_measurable x y a)

theorem threshold_probability_reindex (D : System (Fin n) ℚ) (x : Fin n) (c : ℚ) (a : Answer) :
    (uniformMeasure (indexed D).toReal).real (LocalSelection.thresholdEvent (index D x) c a) =
      (uniformMeasure D.toReal).real (LocalSelection.thresholdEvent x c a) := by
  have hpre : assignmentEquiv (orderEquiv D) ⁻¹' LocalSelection.thresholdEvent x c a =
      LocalSelection.thresholdEvent (index D x) c a := by
    cases a <;> ext X <;> simp only [LocalSelection.thresholdEvent, mem_preimage,
      mem_ofPred_eq, assignmentEquiv_apply, index]
  change (uniformMeasure (D.toReal.reindex (orderEquiv D))).real _ = _
  rw [← hpre]
  exact uniformMeasure_reindex_real D.toReal (orderEquiv D) _
    (LocalSelection.thresholdEvent_measurable x c a)

theorem coordinate_probability_reindex (D : System (Fin n) ℚ) (x : Fin n)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (uniformMeasure (indexed D).toReal).real {X | X (index D x) ∈ E} =
      (uniformMeasure D.toReal).real {X | X x ∈ E} := by
  have hpre : assignmentEquiv (orderEquiv D) ⁻¹' {X : Fin n → ℝ | X x ∈ E} =
      {X | X (index D x) ∈ E} := by
    ext X
    simp only [mem_preimage, mem_ofPred_eq, assignmentEquiv_apply, index]
  change (uniformMeasure (D.toReal.reindex (orderEquiv D))).real _ = _
  rw [← hpre]
  exact uniformMeasure_reindex_real D.toReal (orderEquiv D) _
    (hE.preimage (measurable_pi_apply x))

theorem select_probability (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (x y : Fin n) (a : Answer) (h : select D k x y = .answer a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤
      (uniformMeasure D.toReal).real (LocalSelection.comparisonEvent x y a) := by
  rw [select_pos D k hk] at h
  have ht := selectTwo_answer D k (pathHeight k) hk x y a h
  rw [twoIntervals_eq_full] at ht
  have hl : LocalSelection.selectTwo D k (alphabet k (pathHeight k))
      (fullSchedule D k (pathHeight k) hk {x, y}) x y = .answer a := by
    unfold LocalSelection.selectTwo
    rw [ht]
  exact LocalSelection.selectTwo_probability D k (alphabet k (pathHeight k))
    (EnclosureParameters.alphabet_pos k (pathHeight k)) hloop hV _ x y a hl

theorem selectThreshold_probability (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (x : Fin n) (c : ℚ) (a : Answer) (h : selectThreshold D k x c = .answer a) :
    1 / 2 - 1 / (100 * (k : ℝ)) ≤
      (uniformMeasure D.toReal).real (LocalSelection.thresholdEvent x c a) := by
  rw [selectThreshold_pos D k hk] at h
  have ht := selectThreshold_answer D k (pathHeight k) hk x c a h
  rw [thresholdIntervals_eq_full] at ht
  have hl : LocalSelection.selectThreshold D k (alphabet k (pathHeight k))
      (fullSchedule D k (pathHeight k) hk {x}) x c = .answer a := by
    unfold LocalSelection.selectThreshold
    rw [ht]
  exact LocalSelection.selectThreshold_probability D k (alphabet k (pathHeight k))
    (EnclosureParameters.alphabet_pos k (pathHeight k)) hloop hV _ x c a hl

theorem central_probabilities (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (x : Fin n) (J : Interval) (h : centralInterval (oneIntervals D k H hk x) = some J) :
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | X x ≤ (J.1 : ℝ)} ∧
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | (J.1 : ℝ) ≤ X x ∧ X x ≤ (J.2 : ℝ)} ∧
    (1 / 4 : ℝ) ≤ (uniformMeasure D.toReal).real {X | (J.2 : ℝ) ≤ X x} := by
  rw [oneIntervals_eq_full] at h
  exact LocalSelection.centralInterval_probabilities D (alphabet k H)
    (EnclosureParameters.alphabet_pos k H) hloop hV (fullSchedule D k H hk {x}) x J h

theorem central_density (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (x : Fin n) (J : Interval) (h : centralInterval (oneIntervals D k H hk x) = some J)
    {c : ℝ} (hc : (J.1 : ℝ) ≤ c ∧ c ≤ (J.2 : ℝ)) :
    1 / (16 * ((J.2 : ℝ) - J.1)) ≤ density D.toReal x c := by
  have hp := central_probabilities D k H hk hloop hV x J h
  have hJ : (J.1 : ℝ) < (J.2 : ℝ) := by exact_mod_cast (centralInterval_certificates h).1
  apply CentralQuantiles.central_interval_lower (density D.toReal x)
    (density_integrable D.toReal x) (density_nonneg D.toReal x)
    (integral_density D.toReal x (nodeVolume_pos D.toReal hV))
    (fun s c t hsc hct => SectionConcavity.density_two_point D.toReal x hsc hct) hJ hc
  · simpa only [← coordinate_probability_eq_integral D.toReal x _ measurableSet_Iic, mem_Iic] using hp.1
  · simpa only [← coordinate_probability_eq_integral D.toReal x _ measurableSet_Icc, mem_Icc] using hp.2.1
  · simpa only [← coordinate_probability_eq_integral D.toReal x _ measurableSet_Ici, mem_Ici] using hp.2.2

theorem weak_endpoints (D : System (Fin n) ℚ) (hD : Normalized D.toReal)
    (hw : ∀ x, D.lower x < D.upper x) : D.WeaklyFeasible D.lower ∧ D.WeaklyFeasible D.upper := by
  have hn : Normalized D := by
    intro x y hxy
    have hh := hD x y hxy
    change (D.lower x : ℝ) ≤ D.lower y ∧ (D.upper x : ℝ) ≤ D.upper y at hh
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  exact ⟨⟨fun x => ⟨le_rfl, (hw x).le⟩, fun x y h => (hn x y h).1⟩,
    ⟨fun x => ⟨(hw x).le, le_rfl⟩, fun x y h => (hn x y h).2⟩⟩

theorem central_interior (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ x, D.lower x < D.upper x) (x : Fin n) (J : Interval)
    (h : centralInterval (oneIntervals D k H hk x) = some J) :
    D.lower x < J.1 ∧ J.2 < D.upper x := by
  rw [oneIntervals_eq_full] at h
  exact LocalSelection.centralInterval_interior D (alphabet k H)
    (fullSchedule D k H hk {x}) x J hl hu hw h

theorem anchorWithHeight_interior (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ x, D.lower x < D.upper x) (x : Fin n) :
    D.lower x < anchorWithHeight D k H hk x ∧ anchorWithHeight D k H hk x < D.upper x := by
  have hi := LocalSelection.anchor_interior D (alphabet k H)
    (fullSchedule D k H hk {x}) x hl hu hw
  simpa only [LocalSelection.anchor, anchorWithHeight, oneIntervals_eq_full] using hi

theorem chooseAnchor_interior (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k)
    (hD : Normalized D.toReal) (hw : ∀ x, D.lower x < D.upper x) (x : Fin n) :
    D.lower x < chooseAnchor D k x ∧ chooseAnchor D k x < D.upper x := by
  rw [chooseAnchor_pos D k hk]
  exact anchorWithHeight_interior D k (pathHeight k) hk (weak_endpoints D hD hw).1 (weak_endpoints D hD hw).2 hw x

theorem central_roundUp_tariff (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ x, D.lower x < D.upper x) (x : Fin n) (J : Interval)
    (hb : 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (h : centralInterval (oneIntervals D k H hk x) = some J) :
    ∃ c : DyadicAnchor, c.coordinate = roundUp J ∧
      (c.1 : ℝ) - 4 < log2 (density D.toReal x (c.coordinate : ℝ)) := by
  have hr := central_interior D k H hk hl hu hw x J h
  have hJ := (centralInterval_certificates h).1
  obtain ⟨c, hc, hlen⟩ := roundUp_anchor (hb.1.trans_lt hr.1) (hr.2.trans_le hb.2) hJ
  refine ⟨c, hc, ?_⟩
  apply central_density_tariff (w := (J.2 : ℝ) - J.1)
  · exact_mod_cast sub_pos.mpr hJ
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hlen
  · apply central_density D k H hk hloop hV x J h
    rw [hc]
    exact ⟨by exact_mod_cast (roundUp_mem hJ).1, by exact_mod_cast (roundUp_mem hJ).2.le⟩

private theorem loop_false_of_rank (D : System (Fin n) ℚ) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ x, D.edge x x = false := by
  intro x
  apply Bool.eq_false_iff.mpr
  exact fun h => Nat.lt_irrefl _ (hrank x x h)

private theorem widths_le_one (D : System (Fin n) ℚ)
    (hb : ∀ x, 0 ≤ D.lower x ∧ D.upper x ≤ 1) : ∀ x, D.upper x - D.lower x ≤ 1 := by
  intro x
  linarith [hb x]

/-- Full anchor specification on original labels and the original density.
The dyadic level belongs to the actual rational value returned by the code. -/
theorem chooseAnchor_spec (D : System (Fin n) ℚ) (k : ℕ) (hk : 64 ≤ k)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hw : ∀ x, D.lower x < D.upper x) (hb : ∀ x, 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ pathHeight k)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) :
    ∃ c : DyadicAnchor, c.coordinate = chooseAnchor D k x ∧
      D.lower x < c.coordinate ∧ c.coordinate < D.upper x ∧
      stopMass k * c.1 - 4 < log2 (density D.toReal x (c.coordinate : ℝ)) := by
  have hk0 : 0 < k := by omega
  have he := weak_endpoints D hD hw
  have hi := chooseAnchor_interior D k hk0 hD hw x
  cases ht : centralInterval (oneIntervals D k (pathHeight k) hk0 x) with
  | none =>
    have hsmall := central_failure_small D hD hV (fun x => (hw x).le) (widths_le_one D hb)
      rank k (pathHeight k) hk0 hrank hheight hdegree x ht
    have hB := ComparableBound.comparableCount_toReal_le D rank (pathHeight k) k hrank hheight hdegree x
    obtain ⟨c, hc, _, htariff⟩ := LocalSelection.middle_roundUp_tariffs D x k
      (neighborhoodBound k (pathHeight k)) hk (neighborhoodBound_pos k (pathHeight k))
      hD hB hV (hw x) (hb x) hsmall
    have hcoord : c.coordinate = chooseAnchor D k x := by
      rw [chooseAnchor_pos D k hk0]
      simpa [anchorWithHeight, Certificates.chooseAnchor, ht] using hc
    rw [← hcoord] at hi
    exact ⟨c, hcoord, hi.1, hi.2, htariff⟩
  | some J =>
    obtain ⟨c, hc, htariff⟩ := central_roundUp_tariff D k (pathHeight k) hk0
      (loop_false_of_rank D rank hrank) hV he.1 he.2 hw x J (hb x) ht
    have hcoord : c.coordinate = chooseAnchor D k x := by
      rw [chooseAnchor_pos D k hk0]
      simpa [anchorWithHeight, Certificates.chooseAnchor, ht] using hc
    rw [← hcoord] at hi
    have hstop : stopMass k ≤ 1 := by
      unfold stopMass
      have hnonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      linarith
    have hdiscount : stopMass k * (c.1 : ℝ) ≤ c.1 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hstop (Nat.cast_nonneg c.1)
    exact ⟨c, hcoord, hi.1, hi.2, (sub_le_sub_right hdiscount 4).trans_lt htariff⟩

/-- Every actual comparison refinement selects a queried original label,
lies in its stored interval, and has both printed density-gain bounds. -/
theorem select_refine_spec (D : System (Fin n) ℚ) (k : ℕ) (hk : 64 ≤ k)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hw : ∀ x, D.lower x < D.upper x) (hb : ∀ x, 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ pathHeight k)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x y z : Fin n) (hne : x ≠ y) (q : ℚ) (h : select D k x y = .refine z q) :
    (z = x ∨ z = y) ∧ ∃ c : DyadicAnchor, c.coordinate = q ∧
      D.lower z < q ∧ q < D.upper z ∧
      (k : ℝ) < log2 (density D.toReal z (q : ℝ)) ∧
      stopMass k * c.1 - 4 < log2 (density D.toReal z (q : ℝ)) := by
  have hk0 : 0 < k := by omega
  rw [select_pos D k hk0] at h
  have hl := selectTwo_refine_label D k (pathHeight k) hk0 x y z q h
  have hs := selectTwo_refine_small D hD hV (fun x => (hw x).le) (widths_le_one D hb)
    rank k (pathHeight k) hk0 hrank hheight hdegree x y z hne q h
  have hB := ComparableBound.comparableCount_toReal_le D rank (pathHeight k) k hrank hheight hdegree z
  obtain ⟨c, hc, hgain, htariff⟩ := LocalSelection.middle_roundUp_tariffs D z k
    (neighborhoodBound k (pathHeight k)) hk (neighborhoodBound_pos k (pathHeight k))
    hD hB hV (hw z) (hb z) hs
  have hcoord : c.coordinate = q := hc.trans hl.2.symm
  have hinside : D.lower z < q ∧ q < D.upper z := by
    rw [hl.2]
    exact roundUp_middleHalf_interior (hw z)
  have hz : z = x ∨ z = y := by
    rw [hl.1]
    exact (min_cases x y).imp And.left And.left
  rw [hcoord] at hgain htariff
  exact ⟨hz, c, hcoord, hinside.1, hinside.2, hgain, htariff⟩

theorem selectThreshold_refine_spec (D : System (Fin n) ℚ) (k : ℕ) (hk : 64 ≤ k)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hw : ∀ x, D.lower x < D.upper x) (hb : ∀ x, 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ pathHeight k)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x z : Fin n) (a q : ℚ) (h : selectThreshold D k x a = .refine z q) :
    z = x ∧ ∃ c : DyadicAnchor, c.coordinate = q ∧
      D.lower z < q ∧ q < D.upper z ∧
      (k : ℝ) < log2 (density D.toReal z (q : ℝ)) ∧
      stopMass k * c.1 - 4 < log2 (density D.toReal z (q : ℝ)) := by
  have hk0 : 0 < k := by omega
  rw [selectThreshold_pos D k hk0] at h
  have hl := selectThreshold_refine_label D k (pathHeight k) hk0 x z a q h
  have hs := selectThreshold_refine_small D hD hV (fun x => (hw x).le) (widths_le_one D hb)
    rank k (pathHeight k) hk0 hrank hheight hdegree x z a q h
  have hB := ComparableBound.comparableCount_toReal_le D rank (pathHeight k) k hrank hheight hdegree z
  obtain ⟨c, hc, hgain, htariff⟩ := LocalSelection.middle_roundUp_tariffs D z k
    (neighborhoodBound k (pathHeight k)) hk (neighborhoodBound_pos k (pathHeight k))
    hD hB hV (hw z) (hb z) hs
  have hcoord : c.coordinate = q := hc.trans hl.2.symm
  have hinside : D.lower z < q ∧ q < D.upper z := by
    rw [hl.2]
    exact roundUp_middleHalf_interior (hw z)
  rw [hcoord] at hgain htariff
  exact ⟨hl.1, c, hcoord, hinside.1, hinside.2, hgain, htariff⟩

end SortingAdversary.Continuous.ArbitraryLabels
