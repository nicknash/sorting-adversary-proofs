import SortingAdversary.Continuous.UniformStages
import SortingAdversary.Continuous.Precision
import SortingAdversary.Continuous.NeighborhoodCertificates

/-!
# Precision of the public continuous routines

These bounds refer to `ArbitraryLabels.select` and `chooseAnchor`, including
the computed topological relabeling and the actual calibrated neighborhood
schedule. Each refinement adds at most `log₂ E_k` fractional digits; this is
the exact input to the stored-state induction in the arithmetic appendix.
-/

namespace SortingAdversary.Continuous.RuntimePrecision

open FiniteAveraging OrderRegion Certificates Precision UniformStages
open EnclosureParameters GraphOrder
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

theorem indexed_onGrid (D : System (Fin n) ℚ) (F : ℕ) (hD : BoundsOnGrid D F) :
    BoundsOnGrid (indexed D) F :=
  ⟨fun x => hD.1 (orderEquiv D x), fun x => hD.2 (orderEquiv D x)⟩

theorem wordCount_le_budget (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k) :
    (enclose (indexed D) (alphabet k (ArbitraryLabels.pathHeight k))
      (ArbitraryLabels.schedule D k (ArbitraryLabels.pathHeight k) hk Q)).length ≤
      enumerationBudget k hk := by
  have hi := calibratedEnclose_length_le (indexed D) k (ArbitraryLabels.pathHeight k)
    (Q.image (ArbitraryLabels.index D)) ((Finset.card_image_le).trans hQ)
    (ArbitraryLabels.indexed_degree D k hdegree)
    (CertificateSuccess.accuracy k (neighborhoodBound k (ArbitraryLabels.pathHeight k))
      (ArbitraryLabels.widthThreshold k (ArbitraryLabels.pathHeight k)))
    (CertificateSuccess.failure k)
    (CertificateSuccess.accuracy_pos hk _ (ArbitraryLabels.widthThreshold_pos _ _))
    (CertificateSuccess.failure_pos hk)
  simpa only [calibratedEnclose_eq_enclose, ArbitraryLabels.schedule,
    CertificateSuccess.certificateSchedule, enumerationBudget] using hi

theorem localWordCount_le_budget (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k) :
    (enclose D (alphabet k (ArbitraryLabels.pathHeight k))
      (Neighborhood.fullSchedule D k (ArbitraryLabels.pathHeight k) hk
        (ArbitraryLabels.widthThreshold k (ArbitraryLabels.pathHeight k))
        (ArbitraryLabels.widthThreshold_pos _ _) Q)).length ≤ enumerationBudget k hk :=
  Neighborhood.fullEnclose_length_bound D k (ArbitraryLabels.pathHeight k) hk _ _ Q hQ hdegree

theorem oneIntervals_onGrid (D : System (Fin n) ℚ) (F k : ℕ) (hk : 0 < k)
    (x : Fin n) (hD : BoundsOnGrid D F)
    (hdegree : ∀ y, (neighbors D.edge y).card ≤ k)
    {J : Interval} (hJ : J ∈ ArbitraryLabels.oneIntervals D k (ArbitraryLabels.pathHeight k) hk x) :
    OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) J.1 ∧
    OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) J.2 := by
  rw [ArbitraryLabels.oneIntervals, Neighborhood.oneIntervals_full] at hJ
  obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hJ
  have hg := endpoint_precision_log D F
    (alphabetExponent k (ArbitraryLabels.pathHeight k))
    (Neighborhood.fullSchedule D k (ArbitraryLabels.pathHeight k) hk
      (ArbitraryLabels.widthThreshold k (ArbitraryLabels.pathHeight k))
      (ArbitraryLabels.widthThreshold_pos _ _) {x}) hD hI x
  have hl := Nat.log_mono_right (b := 2) (localWordCount_le_budget D k hk {x} (by simp) hdegree)
  exact ⟨grid_mono hg.1 (Nat.add_le_add_left hl F), grid_mono hg.2 (Nat.add_le_add_left hl F)⟩

theorem indexed_lower_weak (D : System (Fin n) ℚ) (h : D.WeaklyFeasible D.lower) :
    (indexed D).WeaklyFeasible (indexed D).lower :=
  ⟨fun x => h.1 (orderEquiv D x), fun x y he => h.2 (orderEquiv D x) (orderEquiv D y) he⟩

theorem indexed_upper_weak (D : System (Fin n) ℚ) (h : D.WeaklyFeasible D.upper) :
    (indexed D).WeaklyFeasible (indexed D).upper :=
  ⟨fun x => h.1 (orderEquiv D x), fun x y he => h.2 (orderEquiv D x) (orderEquiv D y) he⟩

/-- The public routine, with the manuscript's fixed calibration, returns a
dyadic anchor with at most `Λ + log₂ E_k` fractional digits. -/
theorem chooseAnchor_onGrid (D : System (Fin n) ℚ) (F k : ℕ) (hk : 0 < k)
    (x : Fin n) (hD : BoundsOnGrid D F)
    (hdegree : ∀ y, (neighbors D.edge y).card ≤ k)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ y, D.lower y < D.upper y) (h0 : 0 ≤ D.lower x) (h1 : D.upper x ≤ 1) :
    OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) (ArbitraryLabels.chooseAnchor D k x) := by
  rw [ArbitraryLabels.chooseAnchor_pos D k hk x]
  apply Precision.chooseAnchor_onGrid (hD.1 x) (hD.2 x)
  · exact fun I hI => oneIntervals_onGrid D F k hk x hD hdegree hI
  · intro I hI
    rw [ArbitraryLabels.oneIntervals, Neighborhood.oneIntervals_full] at hI
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
    exact ⟨enclose_right_gt_lower D (alphabet k (ArbitraryLabels.pathHeight k)) _ hu hw he x,
      enclose_left_lt_upper D (alphabet k (ArbitraryLabels.pathHeight k)) _ hl hw he x⟩
  · exact h0
  · exact h1
  · exact hw x
  · exact Nat.add_le_add_left (enumerationBudget_log_ge_two k hk) F

theorem select_refine_onGrid (D : System (Fin n) ℚ) (F k : ℕ) (hk : 0 < k)
    (x y z : Fin n) (c : ℚ) (hD : BoundsOnGrid D F)
    (hunit : ∀ v, 0 ≤ D.lower v ∧ D.upper v ≤ 1)
    (hw : ∀ v, D.lower v < D.upper v)
    (h : ArbitraryLabels.select D k x y = .refine z c) :
    OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) c := by
  rw [ArbitraryLabels.select_pos D k hk x y] at h
  have hc := (ArbitraryLabels.selectTwo_refine_label D k (ArbitraryLabels.pathHeight k) hk x y z c h).2
  rw [hc]
  exact grid_mono (middleHalf_anchor_onGrid (hD.1 z) (hD.2 z) (hunit z).1 (hunit z).2 (hw z))
    (Nat.add_le_add_left (enumerationBudget_log_ge_two k hk) F)

theorem selectThreshold_refine_onGrid (D : System (Fin n) ℚ) (F k : ℕ) (hk : 0 < k)
    (x z : Fin n) (a c : ℚ) (hD : BoundsOnGrid D F)
    (hunit : ∀ v, 0 ≤ D.lower v ∧ D.upper v ≤ 1)
    (hw : ∀ v, D.lower v < D.upper v)
    (h : ArbitraryLabels.selectThreshold D k x a = .refine z c) :
    OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) c := by
  rw [ArbitraryLabels.selectThreshold_pos D k hk x a] at h
  have hc := (ArbitraryLabels.selectThreshold_refine_label D k (ArbitraryLabels.pathHeight k) hk x z a c h).2
  rw [hc]
  exact grid_mono (middleHalf_anchor_onGrid (hD.1 z) (hD.2 z) (hunit z).1 (hunit z).2 (hw z))
    (Nat.add_le_add_left (enumerationBudget_log_ge_two k hk) F)

theorem normalized_reset_onGrid (D : System (Fin n) ℚ) (F k : ℕ) (hk : 0 < k)
    (x : Fin n) (c : ℚ) (hD : BoundsOnGrid D F)
    (hc : OnDyadicGrid (F + Nat.log 2 (enumerationBudget k hk)) c) :
    BoundsOnGrid (ArbitraryLabels.normalize (TreeState.resetCoordinate D x c))
      (F + Nat.log 2 (enumerationBudget k hk)) := by
  apply normalize_onGrid
  exact resetCoordinate_onGrid _ _ _ _ (bounds_mono hD (Nat.le_add_right _ _)) hc

end SortingAdversary.Continuous.RuntimePrecision
