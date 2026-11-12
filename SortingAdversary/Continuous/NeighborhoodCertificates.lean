import SortingAdversary.Continuous.Neighborhood
import SortingAdversary.Continuous.LocalSelectionProofs

/-!
# Certificates computed wholly inside the retained neighborhood

Success is proved using the induced graph's inherited geometric and degree
bounds. Soundness is interpreted in the original graph, through exact equality
with full-graph endpoint runs along the embedded local schedule.
-/

namespace SortingAdversary.Continuous.Neighborhood

open FiniteAveraging OrderRegion GraphOrder EnclosureParameters CertificateSuccess Certificates
open InducedEnclosure MeasureTheory Set
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

def twoIntervals (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (x y : Fin n) : List ComparisonIntervals :=
  LocalSelection.comparisonList (system D k H hk w hw {x, y}) (alphabet k H)
    (schedule D k H hk w hw {x, y})
    (query D k H hk w hw {x, y} x (by simp)) (query D k H hk w hw {x, y} y (by simp))

def thresholdIntervals (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (x : Fin n) (c : ℚ) : List ComparisonIntervals :=
  LocalSelection.thresholdList (system D k H hk w hw {x}) (alphabet k H)
    (schedule D k H hk w hw {x}) (query D k H hk w hw {x} x (by simp)) c

def oneIntervals (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (x : Fin n) : List Interval :=
  (enclose (system D k H hk w hw {x}) (alphabet k H) (schedule D k H hk w hw {x})).map
    (fun I => I (query D k H hk w hw {x} x (by simp)))

/-- This schedule is used only to interpret the finite local computation in
the original region; constructing the local interval lists does not use it. -/
def fullSchedule (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : List (Fin n) :=
  (schedule D k H hk w hw Q).map (embedding D k H hk w hw Q)

theorem twoIntervals_full (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (x y : Fin n) : twoIntervals D k H hk w hw x y =
      LocalSelection.comparisonList D (alphabet k H) (fullSchedule D k H hk w hw {x, y}) x y := by
  unfold twoIntervals LocalSelection.comparisonList
  rw [enclose_full]
  simp only [fullSchedule, List.map_map, Function.comp_def, embedding_query]

theorem thresholdIntervals_full (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (w : ℚ) (hw : 0 < w) (x : Fin n) (c : ℚ) : thresholdIntervals D k H hk w hw x c =
      LocalSelection.thresholdList D (alphabet k H) (fullSchedule D k H hk w hw {x}) x c := by
  unfold thresholdIntervals LocalSelection.thresholdList
  rw [enclose_full]
  simp only [fullSchedule, List.map_map, Function.comp_def, embedding_query]

theorem oneIntervals_full (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (x : Fin n) : oneIntervals D k H hk w hw x =
      (enclose D (alphabet k H) (fullSchedule D k H hk w hw {x})).map (fun I => I x) := by
  unfold oneIntervals
  rw [enclose_full]
  simp only [fullSchedule, List.map_map, Function.comp_def, embedding_query]

theorem two_test_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k)
    (x y : Fin n) (hne : x ≠ y) (w : ℚ) (hw : 0 < w)
    (hwide : w ≤ D.upper x - D.lower x ∨ w ≤ D.upper y - D.lower y) :
    ∃ a, selectAnswer k (twoIntervals D k H hk w hw x y) = some a := by
  let E := system D k H hk w hw {x, y}
  let e := embedding D k H hk w hw {x, y}
  let a := query D k H hk w hw {x, y} x (by simp)
  let b := query D k H hk w hw {x, y} y (by simp)
  have hab : a ≠ b := by
    intro he
    apply hne
    simpa only [a, b, e, embedding_query] using congrArg e he
  have hs := CertificateSuccess.comparison_succeeds E
    (normalized D k H hk w hw {x, y} hD) (volume_pos D k H hk w hw {x, y} hV)
    (ordered D k H hk w hw {x, y} rank hrank)
    (fun z => hwidth (e z)) (fun z => hunit (e z)) (fun z => rank (e z))
    k H (neighborhoodBound k H) hk (fun u v h => hrank (e u) (e v) h)
    (fun z => hheight (e z)) (degree D k H hk w hw {x, y} hdegree) a b hab
    (comparable_bound D k H hk w hw {x, y} rank hrank hheight hdegree a)
    (comparable_bound D k H hk w hw {x, y} rank hrank hheight hdegree b)
    w hw (by simpa only [E, a, b, lower_query, upper_query] using hwide)
  simpa only [twoIntervals, schedule, queries_pair, E, a, b] using hs

theorem threshold_test_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k)
    (x : Fin n) (w : ℚ) (hw : 0 < w) (hwide : w ≤ D.upper x - D.lower x) (c : ℚ) :
    ∃ a, selectAnswer k (thresholdIntervals D k H hk w hw x c) = some a := by
  let E := system D k H hk w hw {x}
  let e := embedding D k H hk w hw {x}
  let a := query D k H hk w hw {x} x (by simp)
  have hs := CertificateSuccess.threshold_succeeds E
    (normalized D k H hk w hw {x} hD) (volume_pos D k H hk w hw {x} hV)
    (ordered D k H hk w hw {x} rank hrank)
    (fun z => hwidth (e z)) (fun z => hunit (e z)) (fun z => rank (e z))
    k H (neighborhoodBound k H) hk (fun u v h => hrank (e u) (e v) h)
    (fun z => hheight (e z)) (degree D k H hk w hw {x} hdegree) a
    (comparable_bound D k H hk w hw {x} rank hrank hheight hdegree a)
    w hw (by simpa only [E, a, lower_query, upper_query] using hwide) c
  simpa only [thresholdIntervals, schedule, queries_singleton, E, a] using hs

theorem central_test_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k)
    (x : Fin n) (w : ℚ) (hw : 0 < w) (hwide : w ≤ D.upper x - D.lower x) :
    centralInterval (oneIntervals D k H hk w hw x) = some (centralCandidate (oneIntervals D k H hk w hw x)) := by
  let E := system D k H hk w hw {x}
  let e := embedding D k H hk w hw {x}
  let a := query D k H hk w hw {x} x (by simp)
  have hs := CertificateSuccess.central_succeeds E
    (normalized D k H hk w hw {x} hD) (volume_pos D k H hk w hw {x} hV)
    (ordered D k H hk w hw {x} rank hrank)
    (fun z => hwidth (e z)) (fun z => hunit (e z)) (fun z => rank (e z))
    k H (neighborhoodBound k H) hk (fun u v h => hrank (e u) (e v) h)
    (fun z => hheight (e z)) (degree D k H hk w hw {x} hdegree) a
    (comparable_bound D k H hk w hw {x} rank hrank hheight hdegree a)
    w hw (by simpa only [E, a, lower_query, upper_query] using hwide)
  simpa only [oneIntervals, schedule, queries_singleton, E, a] using hs

theorem enclose_length_bound (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k) :
    (enclose (system D k H hk w hw Q) (alphabet k H) (schedule D k H hk w hw Q)).length ≤
      enumerationBound k H (accuracy k (neighborhoodBound k H) w) (failure k)
        (accuracy_pos hk _ hw) (failure_pos hk) := by
  exact calibratedEnclose_length_le (system D k H hk w hw Q) k H (queries D k H hk w hw Q)
    ((queries_card D k H hk w hw Q).trans hQ) (degree D k H hk w hw Q hdegree)
    _ _ _ _

theorem fullEnclose_length_bound (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ 2)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k) :
    (enclose D (alphabet k H) (fullSchedule D k H hk w hw Q)).length ≤
      enumerationBound k H (accuracy k (neighborhoodBound k H) w) (failure k)
        (accuracy_pos hk _ hw) (failure_pos hk) := by
  have h := enclose_length_bound D k H hk w hw Q hQ hdegree
  rw [enclose_full, List.length_map] at h
  exact h

end SortingAdversary.Continuous.Neighborhood
