import SortingAdversary.Continuous.PolylogEnclosure
import SortingAdversary.Continuous.NeighborhoodCertificates

/-!
# Success of the local tests on outward-rounded intervals

The tests enumerate only the retained neighborhood. Its entries on the queried
coordinates are exactly the projections of the full system along the embedded
schedule. This transports its bad-width count to the original region, where
the existing small-difference and finite-count estimates apply.
-/

namespace SortingAdversary.Continuous.PolylogSelection

open FiniteAveraging Certificates CertificateSuccess EnclosureParameters OrderRegion
open MeasureTheory Set Optimal.GraphBalls
open PolylogEnclosure (localList roundedEnclose mesh)
open Neighborhood (query embedding queries embedding_query)

variable {n : ℕ} (D : System (Fin n) ℚ) (F k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)

def twoIntervals (x y : Fin n) : List ComparisonIntervals :=
  pairEntries (localList D F k H hk w hw {x,y})
    (query D k H hk (w/2) (by positivity) {x,y} x (by simp))
    (query D k H hk (w/2) (by positivity) {x,y} y (by simp))

def thresholdIntervals (x : Fin n) (c : ℚ) : List ComparisonIntervals :=
  thresholdEntries (localList D F k H hk w hw {x})
    (query D k H hk (w/2) (by positivity) {x} x (by simp)) c

def oneIntervals (x : Fin n) : List Interval :=
  (localList D F k H hk w hw {x}).map (fun I =>
    I (query D k H hk (w/2) (by positivity) {x} x (by simp)))

/-- The full list is used only in the proof. -/
def fullList (Q : Finset (Fin n)) :=
  roundedEnclose D F (alphabet k H) (Neighborhood.fullSchedule D k H hk (w/2) (by positivity) Q)

theorem twoIntervals_full (x y : Fin n) :
    twoIntervals D F k H hk w hw x y = pairEntries (fullList D F k H hk w hw {x,y}) x y := by
  simp only [twoIntervals, pairEntries, PolylogEnclosure.localList_full, List.map_map,
    Function.comp_def, embedding_query, fullList, Neighborhood.fullSchedule]

theorem thresholdIntervals_full (x : Fin n) (c : ℚ) :
    thresholdIntervals D F k H hk w hw x c = thresholdEntries (fullList D F k H hk w hw {x}) x c := by
  simp only [thresholdIntervals, thresholdEntries, PolylogEnclosure.localList_full, List.map_map,
    Function.comp_def, embedding_query, fullList, Neighborhood.fullSchedule]

theorem oneIntervals_full (x : Fin n) :
    oneIntervals D F k H hk w hw x = (fullList D F k H hk w hw {x}).map (fun I => I x) := by
  simp only [oneIntervals, PolylogEnclosure.localList_full, List.map_map,
    Function.comp_def, embedding_query, fullList, Neighborhood.fullSchedule]

theorem fullList_pos (Q : Finset (Fin n)) : 0 < (fullList D F k H hk w hw Q).length := by
  rw [fullList, PolylogEnclosure.roundedEnclose_length]
  exact pow_pos (alphabet_pos k H) _

theorem fullList_bounds (Q : Finset (Fin n)) (hloop : ∀ x, D.edge x x = false)
    (hV : 0 < volume (region D.toReal)) : BoundsEvents D (fullList D F k H hk w hw Q) :=
  PolylogEnclosure.roundedEnclose_probability D F _ (alphabet_pos k H) hloop hV _

private theorem fullList_width (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (hdegree : ∀ x, (neighbors D.edge x).card ≤ k)
    (hu : mesh F ≤ accuracy k (neighborhoodBound k H) w / 4) :
    let L := fullList D F k H hk w hw Q
    (L.countP (badWidth Q (accuracy k (neighborhoodBound k H) w)) : ℚ) / L.length ≤ failure k := by
  have h := PolylogEnclosure.localList_width_probability D F k H hk w hw Q
    hwidth hunit rank hrank hheight hdegree hQ hu
  let e := embedding D k H hk (w/2) (by positivity) Q
  let q := queries D k H hk (w/2) (by positivity) Q
  have eqp (δ : ℚ) (I : Fin n → ℚ × ℚ) : badWidth q δ (I ∘ e) = badWidth Q δ I := by
    apply Bool.eq_iff_iff.mpr
    simp only [badWidth, decide_eq_true_eq]
    constructor
    · rintro ⟨z,hz,hwz⟩
      exact ⟨e z, (Neighborhood.mem_queries ..).1 hz, hwz⟩
    · rintro ⟨x,hx,hxx⟩
      let z := query D k H hk (w/2) (by positivity) Q x hx
      have he : e z = x := embedding_query ..
      exact ⟨z, (Neighborhood.mem_queries ..).2 (he ▸ hx), by simpa [Function.comp_def, he] using hxx⟩
  change ((localList D F k H hk w hw Q).countP (badWidth q _) : ℚ) /
      (localList D F k H hk w hw Q).length ≤ failure k at h
  rw [PolylogEnclosure.localList_full] at h
  simp only [List.length_map, List.countP_map] at h
  change (((fullList D F k H hk w hw Q).countP (fun I => badWidth q _ (I ∘ e)) : ℕ) : ℚ) / _ ≤ _ at h
  simpa only [eqp, fullList, Neighborhood.fullSchedule] using h

private theorem loopless (rank : Fin n → ℕ) (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (x : Fin n) : D.edge x x = false := Bool.eq_false_iff.mpr (fun h => (hrank x x h).false)

variable (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
  (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
  (rank : Fin n → ℕ) (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
  (hheight : ∀ x, rank x + 1 ≤ H) (hdegree : ∀ x, (neighbors D.edge x).card ≤ k)
  (hu : mesh F ≤ accuracy k (neighborhoodBound k H) w / 4)

include hD hV hwidth hunit rank hrank hheight hdegree hu

theorem two_test_succeeds (x y : Fin n) (hne : x ≠ y)
    (hBx : ComparableDensity.comparableCount D.toReal x ≤ neighborhoodBound k H)
    (hBy : ComparableDensity.comparableCount D.toReal y ≤ neighborhoodBound k H)
    (hwide : w ≤ D.upper x - D.lower x ∨ w ≤ D.upper y - D.lower y) :
    ∃ a, selectAnswer k (twoIntervals D F k H hk w hw x y) = some a := by
  let L := fullList D F k H hk w hw {x,y}
  have hpos := fullList_pos D F k H hk w hw {x,y}
  have hb := fullList_width D F k H hk w hw {x,y} (by simp [hne]) hwidth hunit rank hrank hheight hdegree hu
  have hs := fullList_bounds D F k H hk w hw {x,y} (loopless D rank hrank) hV
  rw [twoIntervals_full]
  apply selectAnswer_succeeds
  · apply List.ne_nil_of_length_pos
    simpa only [pairEntries, List.length_map] using hpos
  · change 1 - error k ≤ _
    rcases hwide with hx | hy
    · have hm := comparison_mass_of_list D hV hD L hpos hs {x,y} x y (by simp) (by simp)
        hne _ hBx (by linarith) _ _ (accuracy_pos hk _ hw).le hb
      linarith [comparison_error_le hk (neighborhoodBound k H) hw hx]
    · have hm := comparison_mass_of_list D hV hD L hpos hs {x,y} y x (by simp) (by simp)
        hne.symm _ hBy (by linarith) _ _ (accuracy_pos hk _ hw).le hb
      have h' : 1 - error k ≤ lowerFraction (pairEntries L y x) +
          upperFraction (pairEntries L y x) := by
        linarith [comparison_error_le hk (neighborhoodBound k H) hw hy]
      simpa only [pairEntries, lowerFraction, upperFraction, separated, reverseSeparated,
        List.countP_map, List.length_map, Function.comp_def, add_comm, L] using h'

private theorem one_crossing (x : Fin n)
    (hB : ComparableDensity.comparableCount D.toReal x ≤ neighborhoodBound k H)
    (hwide : w ≤ D.upper x - D.lower x) (c : ℚ) :
    let L := fullList D F k H hk w hw {x}
    (crossingCount (L.map (fun I => I x)) c : ℚ) / L.length ≤ 3 * error k / 4 := by
  have hb := fullList_width D F k H hk w hw {x} (by simp) hwidth hunit rank hrank hheight hdegree hu
  have hs := fullList_bounds D F k H hk w hw {x} (loopless D rank hrank) hV
  exact (crossing_fraction_of_list D hV hD _ (fullList_pos D F k H hk w hw {x}) hs {x} x
    (by simp) _ hB (by linarith) _ _ (accuracy_pos hk _ hw).le hb c).trans
      (crossing_error_le hk _ hw hwide)

theorem threshold_test_succeeds (x : Fin n)
    (hB : ComparableDensity.comparableCount D.toReal x ≤ neighborhoodBound k H)
    (hwide : w ≤ D.upper x - D.lower x) (c : ℚ) :
    ∃ a, selectAnswer k (thresholdIntervals D F k H hk w hw x c) = some a := by
  have hc := one_crossing D F k H hk w hw hD hV hwidth hunit rank hrank hheight hdegree hu x hB hwide c
  have hn := fullList_pos D F k H hk w hw {x}
  have hm := threshold_mass_of_list _ hn x c
  rw [thresholdIntervals_full]
  apply selectAnswer_succeeds
  · exact List.ne_nil_of_length_pos (by simpa only [thresholdEntries, List.length_map] using hn)
  · change 1 - error k ≤ _
    dsimp only at hc
    linarith [error_pos hk]

theorem central_test_succeeds (x : Fin n)
    (hB : ComparableDensity.comparableCount D.toReal x ≤ neighborhoodBound k H)
    (hwide : w ≤ D.upper x - D.lower x) :
    let L := oneIntervals D F k H hk w hw x
    centralInterval L = some (centralCandidate L) := by
  dsimp only
  rw [oneIntervals_full]
  let U := fullList D F k H hk w hw {x}
  let L := U.map fun I => I x
  have hN : 0 < L.length := by
    simpa only [L, List.length_map, U] using fullList_pos D F k H hk w hw {x}
  let E := Neighborhood.system D k H hk (w/2) (by positivity) {x}
  let q := Neighborhood.queries D k H hk (w/2) (by positivity) {x}
  have hq : q.Nonempty := by
    rw [show q = _ from Neighborhood.queries_singleton D k H hk (w/2) (by positivity) x]
    simp
  have hf := calibratedEnclose_length_dvd_four E k H q hq
    (accuracy k (neighborhoodBound k H) (w/2)) (failure k)
    (accuracy_pos hk _ (by positivity)) (failure_pos hk)
  have hfour : 4 ∣ L.length := by
    simpa only [L,U,fullList,List.length_map,PolylogEnclosure.roundedEnclose_length,
      Neighborhood.fullSchedule, Neighborhood.schedule, certificateSchedule,
      calibratedEnclose_eq_enclose, enclose_length, E, q] using hf
  apply centralInterval_succeeds L hN hfour
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hI
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hJ
    have b := PolylogEnclosure.roundedEntry_bounds D F (alphabet k H)
      (Neighborhood.fullSchedule D k H hk (w/2) (by positivity) {x}) t x
    have valid := enclose_valid D (alphabet k H) _ hwidth _ (List.mem_map.mpr ⟨t,ht,rfl⟩) x
    exact b.1.1.trans (valid.trans b.2.1)
  · intro c
    have hc := one_crossing D F k H hk w hw hD hV hwidth hunit rank hrank hheight hdegree hu x hB hwide c
    have hc' : (crossingCount L c : ℚ) / L.length ≤ 1/8 := by
      simpa only [L, List.length_map] using hc.trans (crossing_error_small hk)
    have hn : (0 : ℚ) < L.length := by exact_mod_cast hN
    have h := (div_le_iff₀ hn).mp hc'
    exact_mod_cast (show 8 * (crossingCount L c : ℚ) ≤ L.length by linarith)

end SortingAdversary.Continuous.PolylogSelection
