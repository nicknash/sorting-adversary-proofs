import SortingAdversary.Continuous.LocalEnclosure
import SortingAdversary.Continuous.Certificates

/-!
# Executable local selection from finite digit lists

This file connects the actual `Enclose` enumerator to the actual interval
certificate tests. The caller supplies a retained graph and its finite update
schedule; the geometric calibration and construction of that neighbourhood
remain separate from these executable routines.

`selectTwo` breaks ties in favour of its first argument and refines the smaller
queried label on failure. `selectThreshold` puts the free coordinate first.
`anchor` runs the one-coordinate central test before its middle-half fallback.
-/

namespace SortingAdversary.Continuous.LocalSelection

open FiniteAveraging Certificates

inductive Result (n : ℕ) where
  | answer (a : Answer)
  | refine (x : Fin n) (c : ℚ)
  deriving DecidableEq, Repr

def comparisonList {n : ℕ} (D : System (Fin n) ℚ) (S : ℕ)
    (schedule : List (Fin n)) (x y : Fin n) : List ComparisonIntervals :=
  (enclose D S schedule).map (fun I => (I x, I y))

def thresholdList {n : ℕ} (D : System (Fin n) ℚ) (S : ℕ)
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) : List ComparisonIntervals :=
  (enclose D S schedule).map (fun I => (I x, (c, c)))

def selectTwo {n : ℕ} (D : System (Fin n) ℚ) (k S : ℕ)
    (schedule : List (Fin n)) (x y : Fin n) : Result n :=
  match selectAnswer k (comparisonList D S schedule x y) with
  | some a => .answer a
  | none =>
    let z := min x y
    .refine z (roundUp (middleHalf (D.lower z) (D.upper z)))

def selectThreshold {n : ℕ} (D : System (Fin n) ℚ) (k S : ℕ)
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) : Result n :=
  match selectAnswer k (thresholdList D S schedule x c) with
  | some a => .answer a
  | none => .refine x (roundUp (middleHalf (D.lower x) (D.upper x)))

def anchor {n : ℕ} (D : System (Fin n) ℚ) (S : ℕ)
    (schedule : List (Fin n)) (x : Fin n) : ℚ :=
  chooseAnchor (D.lower x) (D.upper x) ((enclose D S schedule).map (fun I => I x))

theorem selectTwo_refine {n : ℕ} (D : System (Fin n) ℚ) (k S : ℕ)
    (schedule : List (Fin n)) (x y z : Fin n) (c : ℚ)
    (hw : ∀ v, D.lower v < D.upper v)
    (h : selectTwo D k S schedule x y = .refine z c) :
    (z = x ∨ z = y) ∧ D.lower z < c ∧ c < D.upper z := by
  unfold selectTwo at h
  split at h
  · contradiction
  · cases h
    have hz : min x y = x ∨ min x y = y := (min_cases x y).imp And.left And.left
    exact ⟨hz, roundUp_middleHalf_interior (hw _)⟩

theorem selectThreshold_refine {n : ℕ} (D : System (Fin n) ℚ) (k S : ℕ)
    (schedule : List (Fin n)) (x z : Fin n) (c a : ℚ)
    (hw : D.lower x < D.upper x)
    (h : selectThreshold D k S schedule x c = .refine z a) :
    z = x ∧ D.lower z < a ∧ a < D.upper z := by
  unfold selectThreshold at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, roundUp_middleHalf_interior hw⟩

theorem selectTwo_certificate {n : ℕ} (D : System (Fin n) ℚ) (k S : ℕ)
    (schedule : List (Fin n)) (x y : Fin n) (a : Answer)
    (h : selectTwo D k S schedule x y = .answer a) :
    1 / 2 - 1 / (100 * (k : ℚ)) ≤
      match a with
      | .less => lowerFraction (comparisonList D S schedule x y)
      | .greater => upperFraction (comparisonList D S schedule x y) := by
  unfold selectTwo at h
  split at h
  · rename_i b hb
    cases h
    cases a <;> exact selectAnswer_certificate k _ _ hb
  · contradiction

theorem selectThreshold_certificate {n : ℕ} (D : System (Fin n) ℚ) (k S : ℕ)
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) (a : Answer)
    (h : selectThreshold D k S schedule x c = .answer a) :
    1 / 2 - 1 / (100 * (k : ℚ)) ≤
      match a with
      | .less => lowerFraction (thresholdList D S schedule x c)
      | .greater => upperFraction (thresholdList D S schedule x c) := by
  unfold selectThreshold at h
  split at h
  · rename_i b hb
    cases h
    cases a <;> exact selectAnswer_certificate k _ _ hb
  · contradiction

theorem anchor_interior {n : ℕ} (D : System (Fin n) ℚ) (S : ℕ)
    (schedule : List (Fin n)) (x : Fin n)
    (hl : D.WeaklyFeasible D.lower) (hu : D.WeaklyFeasible D.upper)
    (hw : ∀ v, D.lower v < D.upper v) :
    D.lower x < anchor D S schedule x ∧ anchor D S schedule x < D.upper x := by
  apply chooseAnchor_interior (hw x)
  intro I hI
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hI
  exact ⟨enclose_right_gt_lower D S schedule hu hw he x,
    enclose_left_lt_upper D S schedule hl hw he x⟩

end SortingAdversary.Continuous.LocalSelection
