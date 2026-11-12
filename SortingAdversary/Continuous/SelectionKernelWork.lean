import SortingAdversary.Continuous.RoundingWork

/-!
# Counted selection after neighborhood preparation

These routines accept stored scalar parameters and a concrete update list.
Every enumeration, finite certificate and fallback rounding operation is
measured. The public adapter additionally charges parameter calibration and
the construction of the retained neighborhood schedule.
-/

namespace SortingAdversary.Continuous.SelectionKernelWork

open FiniteAveraging Precision Certificates EnclosureWork SortingAdversary.Optimal

variable {n : ℕ}

def selectTwo (D : StoredSystem n) (k S : ℕ) (schedule : List (Fin n)) (x y : Fin n) :
    PrimitiveWork.Result (LocalSelection.Result n) :=
  let intervals := EnclosureWork.twoIntervals D S schedule x y
  let certified := CertificateWork.selectAnswer k intervals.value
  match certified.value with
  | some a => ⟨.answer a, intervals.work + certified.work + 1⟩
  | none =>
    let z := min x y
    let anchor := RoundingWork.fallback D.lower[z] D.upper[z]
    ⟨.refine z anchor.value, intervals.work + certified.work + anchor.work + 4⟩

@[simp] theorem selectTwo_value (D : StoredSystem n) (k S : ℕ) (schedule : List (Fin n))
    (x y : Fin n) :
    (selectTwo D k S schedule x y).value = LocalSelection.selectTwo D.system k S schedule x y := by
  simp only [selectTwo, LocalSelection.selectTwo, EnclosureWork.twoIntervals_value,
    CertificateWork.selectAnswer_value]
  cases Certificates.selectAnswer k (LocalSelection.comparisonList D.system S schedule x y) <;>
    simp only [RoundingWork.fallback_value, StoredSystem.system]

theorem selectTwo_work (D : StoredSystem n) (k S F : ℕ) (hS : 0 < S)
    (schedule : List (Fin n)) (x y : Fin n) (hg : BoundsOnGrid D.system F)
    (hunit : ∀ z, 0 ≤ D.system.lower z ∧ D.system.upper z ≤ 1)
    (hwidth : ∀ z, D.system.lower z < D.system.upper z) :
    (selectTwo D k S schedule x y).work ≤
      listBound n S schedule.length + 20 * (S ^ schedule.length + 1) + 6 * F + 38 := by
  have hi := EnclosureWork.twoIntervals_work D S hS schedule x y
  have hc := CertificateWork.selectAnswer_work k (EnclosureWork.twoIntervals D S schedule x y).value
  have he : (EnclosureWork.twoIntervals D S schedule x y).value.length = S ^ schedule.length := by
    rw [EnclosureWork.twoIntervals_value]
    simp only [LocalSelection.comparisonList, List.length_map, enclose_length]
  rw [he] at hc
  have hr := RoundingWork.fallback_work D.lower[min x y] D.upper[min x y] F
    ⟨hg.1 _, hg.2 _⟩ (hunit _).1 (hunit _).2 (hwidth _)
  simp only [selectTwo]
  split <;> dsimp only <;> omega

def selectThreshold (D : StoredSystem n) (k S : ℕ) (schedule : List (Fin n))
    (x : Fin n) (c : ℚ) : PrimitiveWork.Result (LocalSelection.Result n) :=
  let intervals := EnclosureWork.thresholdIntervals D S schedule x c
  let certified := CertificateWork.selectAnswer k intervals.value
  match certified.value with
  | some a => ⟨.answer a, intervals.work + certified.work + 1⟩
  | none =>
    let anchor := RoundingWork.fallback D.lower[x] D.upper[x]
    ⟨.refine x anchor.value, intervals.work + certified.work + anchor.work + 3⟩

@[simp] theorem selectThreshold_value (D : StoredSystem n) (k S : ℕ) (schedule : List (Fin n))
    (x : Fin n) (c : ℚ) :
    (selectThreshold D k S schedule x c).value =
      LocalSelection.selectThreshold D.system k S schedule x c := by
  simp only [selectThreshold, LocalSelection.selectThreshold, EnclosureWork.thresholdIntervals_value,
    CertificateWork.selectAnswer_value]
  cases Certificates.selectAnswer k (LocalSelection.thresholdList D.system S schedule x c) <;>
    simp only [RoundingWork.fallback_value, StoredSystem.system]

theorem selectThreshold_work (D : StoredSystem n) (k S F : ℕ) (hS : 0 < S)
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) (hg : BoundsOnGrid D.system F)
    (hunit : 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1)
    (hwidth : D.system.lower x < D.system.upper x) :
    (selectThreshold D k S schedule x c).work ≤
      listBound n S schedule.length + 20 * (S ^ schedule.length + 1) + 6 * F + 38 := by
  have hi := EnclosureWork.thresholdIntervals_work D S hS schedule x c
  have hc := CertificateWork.selectAnswer_work k (EnclosureWork.thresholdIntervals D S schedule x c).value
  have he : (EnclosureWork.thresholdIntervals D S schedule x c).value.length = S ^ schedule.length := by
    rw [EnclosureWork.thresholdIntervals_value]
    simp only [LocalSelection.thresholdList, List.length_map, enclose_length]
  rw [he] at hc
  have hr := RoundingWork.fallback_work D.lower[x] D.upper[x] F
    ⟨hg.1 _, hg.2 _⟩ hunit.1 hunit.2 hwidth
  simp only [selectThreshold]
  split <;> dsimp only <;> omega

def chooseAnchor (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n)) (x : Fin n) :
    PrimitiveWork.Result ℚ :=
  let intervals := EnclosureWork.oneIntervals D S schedule x
  let anchor := RoundingWork.chooseAnchor D.lower[x] D.upper[x] intervals.value
  ⟨anchor.value, intervals.work + anchor.work + 2⟩

@[simp] theorem chooseAnchor_value (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n))
    (x : Fin n) :
    (chooseAnchor D S schedule x).value = LocalSelection.anchor D.system S schedule x := by
  simp only [chooseAnchor, EnclosureWork.oneIntervals_value, RoundingWork.chooseAnchor_value,
    LocalSelection.anchor, StoredSystem.system]

theorem chooseAnchor_work (D : StoredSystem n) (F s : ℕ)
    (schedule : List (Fin n)) (x : Fin n) (hg : BoundsOnGrid D.system F)
    (hunit : 0 ≤ D.system.lower x ∧ D.system.upper x ≤ 1)
    (hwidth : ∀ z, D.system.lower z < D.system.upper z)
    (hl : D.system.WeaklyFeasible D.system.lower) (hu : D.system.WeaklyFeasible D.system.upper) :
    (chooseAnchor D (2 ^ s) schedule x).work ≤
      listBound n (2 ^ s) schedule.length + 65 * ((2 ^ s) ^ schedule.length + 1) ^ 2 +
        6 * (2 * F + s * schedule.length) + 37 := by
  let L := (EnclosureWork.oneIntervals D (2 ^ s) schedule x).value
  have hlist : ∀ I ∈ L,
      OnDyadicGrid (F + s * schedule.length) I.1 ∧
        OnDyadicGrid (F + s * schedule.length) I.2 := by
    intro I hI
    rw [show L = (enclose D.system (2 ^ s) schedule).map (fun J => J x) from
      EnclosureWork.oneIntervals_value D (2 ^ s) schedule x] at hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    exact enclose_onGrid D.system F s schedule hg hJ x
  have hL : ∀ I ∈ L, D.lower[x] < I.2 ∧ I.1 < D.upper[x] := by
    intro I hI
    rw [show L = (enclose D.system (2 ^ s) schedule).map (fun J => J x) from
      EnclosureWork.oneIntervals_value D (2 ^ s) schedule x] at hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    exact ⟨enclose_right_gt_lower D.system (2 ^ s) schedule hu hwidth hJ x,
      enclose_left_lt_upper D.system (2 ^ s) schedule hl hwidth hJ x⟩
  have hw := RoundingWork.chooseAnchor_work D.lower[x] D.upper[x] L F (F + s * schedule.length)
    ⟨hg.1 _, hg.2 _⟩ hlist hunit.1 hunit.2 (hwidth x) hL
  have hi := EnclosureWork.oneIntervals_work D (2 ^ s) (by positivity) schedule x
  have he : L.length = (2 ^ s) ^ schedule.length := by
    dsimp only [L]
    rw [EnclosureWork.oneIntervals_value]
    simp only [List.length_map, enclose_length]
  rw [he] at hw
  change (EnclosureWork.oneIntervals D (2 ^ s) schedule x).work +
    (RoundingWork.chooseAnchor D.lower[x] D.upper[x] L).work + 2 ≤ _
  omega

/-- A single common polynomial envelope after both the alphabet word count
and its length have passed the stage cap. -/
theorem listBound_polynomial (n S m cap : ℕ) (hm : m ≤ cap) (hE : S ^ m ≤ cap) :
    listBound n S m ≤ 200 * (n + cap + 1) ^ 3 := by
  unfold listBound endpointBound
  have hm' : m + 1 ≤ n + cap + 1 := by omega
  have hn' : n + 1 ≤ n + cap + 1 := by omega
  have hE' : S ^ m ≤ n + cap + 1 := by omega
  have hprod := Nat.mul_le_mul hm' hE'
  have hmn := Nat.mul_le_mul hm (by omega : n + 1 ≤ n + cap + 1)
  have hbig : 1 ≤ n + cap + 1 := by omega
  nlinarith [Nat.mul_le_mul hE' hmn, Nat.zero_le ((n + cap + 1) ^ 2),
    Nat.zero_le ((n + cap + 1) ^ 3)]

end SortingAdversary.Continuous.SelectionKernelWork
