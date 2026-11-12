import SortingAdversary.Continuous.LocalSelectionProofs
import SortingAdversary.Continuous.MarginalMeasure
import SortingAdversary.Continuous.SectionConcavity
import SortingAdversary.Continuous.CentralQuantiles
import SortingAdversary.Continuous.ScalarTariffs

/-!
# Density gains certified by the rational interval tests

A successful central test implies the pointwise density estimate throughout
the interval actually returned by the program. Rounding that interval gives
the reduced dyadic-level tariff. The fallback theorem derives both printed
gain bounds from a small canonical width and the actual comparable-coordinate
density estimate.
-/

namespace SortingAdversary.Continuous.LocalSelection

open FiniteAveraging Certificates OrderRegion Density MeasureTheory Set

variable {n : ℕ}

theorem centralInterval_density (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x : Fin n) (J : Interval)
    (h : centralInterval ((enclose D S schedule).map (fun I => I x)) = some J)
    {c : ℝ} (hc : (J.1 : ℝ) ≤ c ∧ c ≤ (J.2 : ℝ)) :
    1 / (16 * ((J.2 : ℝ) - J.1)) ≤ density D.toReal x c := by
  have hp := centralInterval_probabilities D S hS hloop hV schedule x J h
  have hJ : (J.1 : ℝ) < (J.2 : ℝ) := by
    exact_mod_cast (centralInterval_certificates h).1
  apply CentralQuantiles.central_interval_lower (density D.toReal x)
    (density_integrable D.toReal x) (density_nonneg D.toReal x)
    (integral_density D.toReal x (nodeVolume_pos D.toReal hV))
    (fun s c t hsc hct => SectionConcavity.density_two_point D.toReal x hsc hct) hJ hc
  · simpa only [← coordinate_probability_eq_integral D.toReal x _ measurableSet_Iic, mem_Iic]
      using hp.1
  · simpa only [← coordinate_probability_eq_integral D.toReal x _ measurableSet_Icc, mem_Icc]
      using hp.2.1
  · simpa only [← coordinate_probability_eq_integral D.toReal x _ measurableSet_Ici, mem_Ici]
      using hp.2.2

theorem centralInterval_interior (D : System (Fin n) ℚ) (S : ℕ)
    (schedule : List (Fin n)) (x : Fin n) (J : Interval)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ v, D.lower v < D.upper v)
    (h : centralInterval ((enclose D S schedule).map (fun I => I x)) = some J) :
    D.lower x < J.1 ∧ J.2 < D.upper x := by
  have hN := centralInterval_positive h
  have hc := centralInterval_certificates h
  have hleft : 0 < leftCount ((enclose D S schedule).map (fun I => I x)) J.1 := by omega
  have hright : 0 < rightCount ((enclose D S schedule).map (fun I => I x)) J.2 := by omega
  obtain ⟨I, hI, he⟩ := List.countP_pos_iff.mp hleft
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hI
  obtain ⟨I', hI', he'⟩ := List.countP_pos_iff.mp hright
  obtain ⟨entry', hentry', rfl⟩ := List.mem_map.mp hI'
  exact ⟨(enclose_right_gt_lower D S schedule hu hw hentry x).trans_le
      (of_decide_eq_true he),
    (of_decide_eq_true he').trans_lt (enclose_left_lt_upper D S schedule hl hw hentry' x)⟩

/-- A successful central test supplies an actual dyadic anchor with a strict
gain exceeding its level minus four. -/
theorem central_roundUp_tariff (D : System (Fin n) ℚ) (S : ℕ) (hS : 0 < S)
    (hloop : ∀ x, D.edge x x = false) (hV : 0 < volume (region D.toReal))
    (schedule : List (Fin n)) (x : Fin n) (J : Interval)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ v, D.lower v < D.upper v)
    (hb : 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (h : centralInterval ((enclose D S schedule).map (fun I => I x)) = some J) :
    ∃ c : DyadicAnchor, c.coordinate = roundUp J ∧
      (c.1 : ℝ) - 4 < log2 (density D.toReal x (c.coordinate : ℝ)) := by
  have hr := centralInterval_interior D S schedule x J hl hu hw h
  have hJ := (centralInterval_certificates h).1
  obtain ⟨c, hc, hlen⟩ := roundUp_anchor (hb.1.trans_lt hr.1) (hr.2.trans_le hb.2) hJ
  refine ⟨c, hc, ?_⟩
  apply central_density_tariff (w := (J.2 : ℝ) - J.1)
  · exact_mod_cast (sub_pos.mpr hJ)
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hlen
  · apply centralInterval_density D S hS hloop hV schedule x J h
    rw [hc]
    exact ⟨by exact_mod_cast (roundUp_mem hJ).1, by exact_mod_cast (roundUp_mem hJ).2.le⟩

/-- The fallback is evaluated by the actual `RoundUp` program, and its gain
comes from the actual order-region density. -/
theorem middle_roundUp_tariffs (D : System (Fin n) ℚ) (x : Fin n) (k B : ℕ)
    (hk : 64 ≤ k) (hBpos : 1 ≤ B) (hD : Normalized D.toReal)
    (hB : ComparableDensity.comparableCount D.toReal x ≤ B)
    (hV : 0 < volume (region D.toReal)) (hw : D.lower x < D.upper x)
    (hb : 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (hsmall : D.upper x - D.lower x < 1 / (2 : ℚ) ^ (2 * k * B)) :
    ∃ c : DyadicAnchor, c.coordinate = roundUp (middleHalf (D.lower x) (D.upper x)) ∧
      (k : ℝ) < log2 (density D.toReal x (c.coordinate : ℝ)) ∧
      stopMass k * c.1 - 4 < log2 (density D.toReal x (c.coordinate : ℝ)) := by
  have hJ : (middleHalf (D.lower x) (D.upper x)).1 <
      (middleHalf (D.lower x) (D.upper x)).2 := by dsimp [middleHalf]; linarith
  obtain ⟨c, hc, hlen⟩ := roundUp_anchor
    (show 0 < (middleHalf (D.lower x) (D.upper x)).1 by dsimp [middleHalf]; linarith [hb.1])
    (show (middleHalf (D.lower x) (D.upper x)).2 < 1 by dsimp [middleHalf]; linarith [hb.2]) hJ
  refine ⟨c, hc, ?_⟩
  apply failed_density_tariffs (W := (D.upper x : ℝ) - D.lower x) hk hBpos
  · exact_mod_cast sub_pos.mpr hw
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hsmall
  · apply ComparableDensity.middle_density_lower D.toReal hD x
      (by exact (Rat.cast_lt (K := ℝ)).mpr hw) (nodeVolume_pos D.toReal hV) B hB
    have hm := roundUp_mem hJ
    rw [← hc] at hm
    change ((D.lower x : ℝ) + ((D.upper x : ℝ) - D.lower x) / 4 ≤
      (c.coordinate : ℝ)) ∧ (c.coordinate : ℝ) ≤
        (D.upper x : ℝ) - ((D.upper x : ℝ) - D.lower x) / 4
    exact ⟨by exact_mod_cast hm.1, by exact_mod_cast hm.2.le⟩
  · have heq : (middleHalf (D.lower x) (D.upper x)).2 -
        (middleHalf (D.lower x) (D.upper x)).1 = (D.upper x - D.lower x) / 2 := by
      dsimp [middleHalf]
      ring
    rw [heq] at hlen
    simpa using (Rat.cast_lt (K := ℝ)).mpr hlen

end SortingAdversary.Continuous.LocalSelection
