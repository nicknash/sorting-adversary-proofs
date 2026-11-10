import SortingAdversary.Continuous.GraphOrder
import SortingAdversary.Continuous.CertificateSuccess
import SortingAdversary.Continuous.LocalSelectionProofs
import SortingAdversary.Continuous.NeighborhoodCertificates

/-!
# Executable calibrated selection on the original labels

The program extracts the required induced neighborhood and computes its
topological permutation there. All finite certificates run on this retained
graph, while query orientation and the smallest-label refinement rule refer
to the original labels. The parameters are exactly those
in the paper, with `H` denoting the directed-path vertex bound (the paper uses
`2H` when its tree height is named `H`).

`Neighborhood.enclose_full` identifies these local endpoint calculations with
updates in the full graph, so their probability certificates are interpreted
under the original feasible-region measure.
-/

namespace SortingAdversary.Continuous.ArbitraryLabels

open FiniteAveraging OrderRegion GraphOrder Certificates EnclosureParameters
open MeasureTheory Set

variable {n : ℕ}

def widthThreshold (k H : ℕ) : ℚ := 1 / (2 : ℚ) ^ (2 * k * neighborhoodBound k H)

theorem widthThreshold_pos (k H : ℕ) : 0 < widthThreshold k H := by
  unfold widthThreshold
  positivity

def index (D : System (Fin n) ℚ) (x : Fin n) : Fin n := (orderEquiv D).symm x

def schedule (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (Q : Finset (Fin n)) : List (Fin n) :=
  CertificateSuccess.certificateSchedule (indexed D) k H (neighborhoodBound k H) hk
    (widthThreshold k H) (widthThreshold_pos k H) (Q.image (index D))

def twoIntervals (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x y : Fin n) :
    List ComparisonIntervals :=
  Neighborhood.twoIntervals D k H hk (widthThreshold k H) (widthThreshold_pos k H) x y

def thresholdIntervals (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x : Fin n) (c : ℚ) :
    List ComparisonIntervals :=
  Neighborhood.thresholdIntervals D k H hk (widthThreshold k H) (widthThreshold_pos k H) x c

def oneIntervals (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x : Fin n) : List Interval :=
  Neighborhood.oneIntervals D k H hk (widthThreshold k H) (widthThreshold_pos k H) x

/-- The embedded schedule interprets the local program in the full region;
the runtime interval lists are computed directly on the retained graph. -/
def fullSchedule (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (Q : Finset (Fin n)) : List (Fin n) :=
  Neighborhood.fullSchedule D k H hk (widthThreshold k H) (widthThreshold_pos k H) Q

theorem twoIntervals_eq_full (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x y : Fin n) :
    twoIntervals D k H hk x y =
      LocalSelection.comparisonList D (alphabet k H) (fullSchedule D k H hk {x, y}) x y :=
  Neighborhood.twoIntervals_full D k H hk (widthThreshold k H) (widthThreshold_pos k H) x y

theorem thresholdIntervals_eq_full (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (x : Fin n) (c : ℚ) : thresholdIntervals D k H hk x c =
      LocalSelection.thresholdList D (alphabet k H) (fullSchedule D k H hk {x}) x c :=
  Neighborhood.thresholdIntervals_full D k H hk (widthThreshold k H) (widthThreshold_pos k H) x c

theorem oneIntervals_eq_full (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x : Fin n) :
    oneIntervals D k H hk x = (enclose D (alphabet k H) (fullSchedule D k H hk {x})).map (fun I => I x) :=
  Neighborhood.oneIntervals_full D k H hk (widthThreshold k H) (widthThreshold_pos k H) x

/-- The tie and refinement label are those of the original query. -/
def selectTwoWithHeight (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x y : Fin n) : LocalSelection.Result n :=
  match selectAnswer k (twoIntervals D k H hk x y) with
  | some a => .answer a
  | none =>
    let z := min x y
    .refine z (roundUp (middleHalf (D.lower z) (D.upper z)))

def selectThresholdWithHeight (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x : Fin n) (c : ℚ) :
    LocalSelection.Result n :=
  match selectAnswer k (thresholdIntervals D k H hk x c) with
  | some a => .answer a
  | none => .refine x (roundUp (middleHalf (D.lower x) (D.upper x)))

def anchorWithHeight (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (x : Fin n) : ℚ :=
  chooseAnchor (D.lower x) (D.upper x) (oneIntervals D k H hk x)

theorem indexed_normalized (D : System (Fin n) ℚ) (hD : Normalized D.toReal) :
    Normalized (indexed D).toReal := normalized_reindex D.toReal (orderEquiv D) hD

theorem indexed_volume_pos (D : System (Fin n) ℚ) (hV : 0 < volume (region D.toReal)) :
    0 < volume (region (indexed D).toReal) := by
  change 0 < volume (region (D.toReal.reindex (orderEquiv D)))
  rwa [volume_reindex]

theorem indexed_rank (D : System (Fin n) ℚ) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ x y, (indexed D).edge x y = true → rank (orderEquiv D x) < rank (orderEquiv D y) :=
  fun x y h => hrank _ _ h

theorem indexed_degree (D : System (Fin n) ℚ) (k : ℕ)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k) :
    ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors (indexed D).edge x).card ≤ k := by
  intro x
  rw [indexed, neighbors_reindex_card]
  exact hdegree (orderEquiv D x)

theorem indexed_comparable_bound (D : System (Fin n) ℚ) (rank : Fin n → ℕ) (k H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) : ComparableDensity.comparableCount (indexed D).toReal x ≤ neighborhoodBound k H :=
  ComparableBound.comparableCount_toReal_le (indexed D) (fun x => rank (orderEquiv D x)) H k
    (indexed_rank D rank hrank) (fun x => hheight _) (indexed_degree D k hdegree) x

@[simp] theorem indexed_lower_index (D : System (Fin n) ℚ) (x : Fin n) :
    (indexed D).lower (index D x) = D.lower x := by simp [indexed, System.reindex, index]

@[simp] theorem indexed_upper_index (D : System (Fin n) ℚ) (x : Fin n) :
    (indexed D).upper (index D x) = D.upper x := by simp [indexed, System.reindex, index]

theorem two_test_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x y : Fin n) (hne : x ≠ y)
    (hwide : widthThreshold k H ≤ D.upper x - D.lower x ∨
      widthThreshold k H ≤ D.upper y - D.lower y) :
    ∃ a, selectAnswer k (twoIntervals D k H hk x y) = some a := by
  exact Neighborhood.two_test_succeeds D hD hV hwidth hunit rank k H hk hrank hheight hdegree
    x y hne (widthThreshold k H) (widthThreshold_pos k H) hwide

theorem threshold_test_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) (hwide : widthThreshold k H ≤ D.upper x - D.lower x) (c : ℚ) :
    ∃ a, selectAnswer k (thresholdIntervals D k H hk x c) = some a := by
  exact Neighborhood.threshold_test_succeeds D hD hV hwidth hunit rank k H hk hrank hheight hdegree
    x (widthThreshold k H) (widthThreshold_pos k H) hwide c

theorem central_test_succeeds (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) (hwide : widthThreshold k H ≤ D.upper x - D.lower x) :
    centralInterval (oneIntervals D k H hk x) = some (centralCandidate (oneIntervals D k H hk x)) := by
  exact Neighborhood.central_test_succeeds D hD hV hwidth hunit rank k H hk hrank hheight hdegree
    x (widthThreshold k H) (widthThreshold_pos k H) hwide

theorem selectTwo_answer (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (x y : Fin n) (a : Answer) (h : selectTwoWithHeight D k H hk x y = .answer a) :
    selectAnswer k (twoIntervals D k H hk x y) = some a := by
  unfold selectTwoWithHeight at h
  split at h
  · cases h
    assumption
  · contradiction

theorem selectThreshold_answer (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (x : Fin n) (c : ℚ) (a : Answer) (h : selectThresholdWithHeight D k H hk x c = .answer a) :
    selectAnswer k (thresholdIntervals D k H hk x c) = some a := by
  unfold selectThresholdWithHeight at h
  split at h
  · cases h
    assumption
  · contradiction

theorem selectTwo_refine_label (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (x y z : Fin n) (c : ℚ) (h : selectTwoWithHeight D k H hk x y = .refine z c) :
    z = min x y ∧ c = roundUp (middleHalf (D.lower z) (D.upper z)) := by
  unfold selectTwoWithHeight at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, rfl⟩

theorem selectThreshold_refine_label (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k)
    (x z : Fin n) (a c : ℚ) (h : selectThresholdWithHeight D k H hk x a = .refine z c) :
    z = x ∧ c = roundUp (middleHalf (D.lower z) (D.upper z)) := by
  unfold selectThresholdWithHeight at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, rfl⟩

theorem selectTwo_refine_small (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x y z : Fin n) (hne : x ≠ y) (c : ℚ)
    (h : selectTwoWithHeight D k H hk x y = .refine z c) :
    D.upper z - D.lower z < widthThreshold k H := by
  have hz := (selectTwo_refine_label D k H hk x y z c h).1
  apply lt_of_not_ge
  intro hwide
  have hwide' : widthThreshold k H ≤ D.upper x - D.lower x ∨
      widthThreshold k H ≤ D.upper y - D.lower y := by
    rw [hz] at hwide
    rcases le_total x y with hxy | hyx
    · exact Or.inl (by simpa only [min_eq_left hxy] using hwide)
    · exact Or.inr (by simpa only [min_eq_right hyx] using hwide)
  obtain ⟨a, ha⟩ := two_test_succeeds D hD hV hwidth hunit rank k H hk hrank hheight hdegree x y hne hwide'
  simp [selectTwoWithHeight, ha] at h

theorem selectThreshold_refine_small (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x z : Fin n) (a c : ℚ) (h : selectThresholdWithHeight D k H hk x a = .refine z c) :
    D.upper z - D.lower z < widthThreshold k H := by
  have hz := (selectThreshold_refine_label D k H hk x z a c h).1
  subst z
  apply lt_of_not_ge
  intro hwide
  obtain ⟨b, hb⟩ := threshold_test_succeeds D hD hV hwidth hunit rank k H hk hrank hheight hdegree x hwide a
  simp [selectThresholdWithHeight, hb] at h

theorem central_failure_small (D : System (Fin n) ℚ)
    (hD : Normalized D.toReal) (hV : 0 < volume (region D.toReal))
    (hwidth : ∀ x, D.lower x ≤ D.upper x) (hunit : ∀ x, D.upper x - D.lower x ≤ 1)
    (rank : Fin n → ℕ) (k H : ℕ) (hk : 0 < k)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (SortingAdversary.Optimal.GraphBalls.neighbors D.edge x).card ≤ k)
    (x : Fin n) (h : centralInterval (oneIntervals D k H hk x) = none) :
    D.upper x - D.lower x < widthThreshold k H := by
  apply lt_of_not_ge
  intro hwide
  have hs := central_test_succeeds D hD hV hwidth hunit rank k H hk hrank hheight hdegree x hwide
  rw [h] at hs
  contradiction

/-- The paper's directed-path bound for a tree of height at most `2^k`. -/
def pathHeight (k : ℕ) : ℕ := 2 ^ (k + 1)

/-- Public normalization computes its order from the current Boolean graph. -/
def normalize (D : System (Fin n) ℚ) : System (Fin n) ℚ :=
  OrderRegion.normalize D (rankOrder (graphRank D))

theorem normalize_normalized (D : System (Fin n) ℚ) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) : Normalized (normalize D) :=
  normalize_rankOrder_normalized D (graphRank D) (graphRank_strict D rank hrank)

/-- Total public `Select`; the zero-parameter branch is outside the theorem's
positive-parameter domain and still returns an explicit middle-half point. -/
def select (D : System (Fin n) ℚ) (k : ℕ) (x y : Fin n) : LocalSelection.Result n :=
  if hk : 0 < k then selectTwoWithHeight D k (pathHeight k) hk x y
  else
    let z := min x y
    .refine z (roundUp (middleHalf (D.lower z) (D.upper z)))

def selectThreshold (D : System (Fin n) ℚ) (k : ℕ) (x : Fin n) (c : ℚ) : LocalSelection.Result n :=
  if hk : 0 < k then selectThresholdWithHeight D k (pathHeight k) hk x c
  else .refine x (roundUp (middleHalf (D.lower x) (D.upper x)))

def chooseAnchor (D : System (Fin n) ℚ) (k : ℕ) (x : Fin n) : ℚ :=
  if hk : 0 < k then anchorWithHeight D k (pathHeight k) hk x
  else roundUp (middleHalf (D.lower x) (D.upper x))

@[simp] theorem select_pos (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k) (x y : Fin n) :
    select D k x y = selectTwoWithHeight D k (pathHeight k) hk x y := by simp [select, hk]

@[simp] theorem selectThreshold_pos (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k) (x : Fin n) (c : ℚ) :
    selectThreshold D k x c = selectThresholdWithHeight D k (pathHeight k) hk x c := by
  simp [selectThreshold, hk]

@[simp] theorem chooseAnchor_pos (D : System (Fin n) ℚ) (k : ℕ) (hk : 0 < k) (x : Fin n) :
    chooseAnchor D k x = anchorWithHeight D k (pathHeight k) hk x := by simp [chooseAnchor, hk]

end SortingAdversary.Continuous.ArbitraryLabels
