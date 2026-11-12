import SortingAdversary.Continuous.EnclosureWork

/-!
# Counted finite interval certificates

The certificate implementation evaluates every endpoint test and every list
traversal explicitly. Counted insertion sort computes the same sorted lists
as the semantic merge sort, including repeated endpoints. The conservative
quadratic sorting bound suffices because the admitted parameter bounds the
entire enumeration by the input size.
-/

namespace SortingAdversary.Continuous.CertificateWork

open Certificates SortingAdversary.Optimal

def length {α : Type*} : List α → PrimitiveWork.Result ℕ
  | [] => ⟨0, 1⟩
  | _ :: xs => let r := length xs; ⟨r.value + 1, r.work + 2⟩

@[simp] theorem length_value {α : Type*} (xs : List α) : (length xs).value = xs.length := by
  induction xs <;> simp_all [length]

theorem length_work {α : Type*} (xs : List α) : (length xs).work = 2 * xs.length + 1 := by
  induction xs <;> simp_all [length] <;> omega

def get? {α : Type*} : List α → ℕ → PrimitiveWork.Result (Option α)
  | [], _ => ⟨none, 1⟩
  | x :: _, 0 => ⟨some x, 2⟩
  | _ :: xs, i + 1 => let r := get? xs i; ⟨r.value, r.work + 2⟩

@[simp] theorem get?_value {α : Type*} (xs : List α) (i : ℕ) :
    (get? xs i).value = xs[i]? := by
  induction xs generalizing i with
  | nil => simp [get?]
  | cons x xs ih => cases i <;> simp [get?, ih]

theorem get?_work {α : Type*} (xs : List α) (i : ℕ) :
    (get? xs i).work ≤ 2 * xs.length + 1 := by
  induction xs generalizing i with
  | nil => simp [get?]
  | cons x xs ih => cases i <;> simp only [get?, List.length_cons] <;> grind

def insert (a : ℚ) : List ℚ → PrimitiveWork.Result (List ℚ)
  | [] => ⟨[a], 2⟩
  | b :: bs =>
    if a ≤ b then ⟨a :: b :: bs, 4⟩ else
      let r := insert a bs
      ⟨b :: r.value, r.work + 4⟩

@[simp] theorem insert_value (a : ℚ) (xs : List ℚ) :
    (insert a xs).value = List.orderedInsert (· ≤ ·) a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [insert, List.orderedInsert_cons]; split <;> simp_all

theorem insert_work (a : ℚ) (xs : List ℚ) : (insert a xs).work ≤ 4 * xs.length + 2 := by
  induction xs with
  | nil => simp [insert]
  | cons x xs ih => simp only [insert, List.length_cons]; split <;> dsimp only <;> omega

def sort : List ℚ → PrimitiveWork.Result (List ℚ)
  | [] => ⟨[], 1⟩
  | a :: xs =>
    let tail := sort xs
    let result := insert a tail.value
    ⟨result.value, tail.work + result.work + 1⟩

theorem sort_insertion (xs : List ℚ) :
    (sort xs).value = xs.insertionSort (· ≤ ·) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sort, insert_value, ih, List.insertionSort_cons]

@[simp] theorem sort_value (xs : List ℚ) :
    (sort xs).value = xs.mergeSort (· ≤ ·) := by
  rw [List.mergeSort_eq_insertionSort, sort_insertion]

theorem sort_work (xs : List ℚ) : (sort xs).work ≤ 5 * (xs.length + 1) ^ 2 := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
    have hi := insert_work x (sort xs).value
    have hlen : (sort xs).value.length = xs.length := by simp
    rw [hlen] at hi
    simp only [sort, List.length_cons]
    nlinarith

def selectAnswer (k : ℕ) (L : List ComparisonIntervals) : PrimitiveWork.Result (Option Answer) :=
  if L.isEmpty then ⟨none, 1⟩ else
    let size := length L
    let left := PrimitiveWork.count (fun I => ⟨separated I, 5⟩) L
    let right := PrimitiveWork.count (fun I => ⟨reverseSeparated I, 5⟩) L
    let p := (left.value : ℚ) / size.value
    let q := (right.value : ℚ) / size.value
    let answer := if max p q < 1 / 2 - 1 / (100 * (k : ℚ)) then none
      else if q ≤ p then some Answer.less else some Answer.greater
    ⟨answer, size.work + left.work + right.work + 17⟩

@[simp] theorem selectAnswer_value (k : ℕ) (L : List ComparisonIntervals) :
    (selectAnswer k L).value = Certificates.selectAnswer k L := by
  simp only [selectAnswer, Certificates.selectAnswer]
  split
  · rfl
  · simp only [length_value, PrimitiveWork.count_value, ← List.countP_eq_length_filter,
      lowerFraction, upperFraction]
    rfl

theorem selectAnswer_work (k : ℕ) (L : List ComparisonIntervals) :
    (selectAnswer k L).work ≤ 20 * (L.length + 1) := by
  have hl := PrimitiveWork.count_work_le (fun I : ComparisonIntervals =>
    (⟨separated I, 5⟩ : PrimitiveWork.Result Bool)) L 5 (fun _ _ => le_rfl)
  have hr := PrimitiveWork.count_work_le (fun I : ComparisonIntervals =>
    (⟨reverseSeparated I, 5⟩ : PrimitiveWork.Result Bool)) L 5 (fun _ _ => le_rfl)
  simp only [selectAnswer, length_work]
  split <;> dsimp only <;> omega

def centralCandidate (L : List Interval) : PrimitiveWork.Result Interval :=
  let size := length L
  let upperList := PrimitiveWork.map (fun I : Interval => ⟨I.2, 1⟩) L
  let lowerList := PrimitiveWork.map (fun I : Interval => ⟨I.1, 1⟩) L
  let uppers := sort upperList.value
  let lowers := sort lowerList.value
  let u := get? uppers.value (size.value / 4 - 1)
  let v := get? lowers.value (3 * size.value / 4 - 1)
  ⟨(u.value.getD 0, v.value.getD 0), size.work + upperList.work + lowerList.work +
    uppers.work + lowers.work + u.work + v.work + 10⟩

@[simp] theorem centralCandidate_value (L : List Interval) :
    (centralCandidate L).value = Certificates.centralCandidate L := by
  simp only [centralCandidate, Certificates.centralCandidate, length_value,
    PrimitiveWork.map_value, sort_value, get?_value]

theorem centralCandidate_work (L : List Interval) :
    (centralCandidate L).work ≤ 40 * (L.length + 1) ^ 2 := by
  have hm₁ := PrimitiveWork.map_work_le (fun I : Interval => (⟨I.2, 1⟩ : PrimitiveWork.Result ℚ))
    L 1 (fun _ _ => le_rfl)
  have hm₂ := PrimitiveWork.map_work_le (fun I : Interval => (⟨I.1, 1⟩ : PrimitiveWork.Result ℚ))
    L 1 (fun _ _ => le_rfl)
  have hs₁ := sort_work (PrimitiveWork.map (fun I : Interval => ⟨I.2, 1⟩) L).value
  have hs₂ := sort_work (PrimitiveWork.map (fun I : Interval => ⟨I.1, 1⟩) L).value
  have hg₁ := get?_work (sort (PrimitiveWork.map (fun I : Interval => ⟨I.2, 1⟩) L).value).value
    ((length L).value / 4 - 1)
  have hg₂ := get?_work (sort (PrimitiveWork.map (fun I : Interval => ⟨I.1, 1⟩) L).value).value
    (3 * (length L).value / 4 - 1)
  simp only [PrimitiveWork.map_value, sort_value, List.length_mergeSort, List.length_map]
    at hs₁ hs₂ hg₁ hg₂
  simp only [centralCandidate, length_work, PrimitiveWork.map_value, sort_value]
  nlinarith

def centralInterval (L : List Interval) : PrimitiveWork.Result (Option Interval) :=
  let size := length L
  if size.value = 0 ∨ ¬ 4 ∣ size.value then ⟨none, size.work + 5⟩ else
    let candidate := centralCandidate L
    let inside := PrimitiveWork.count (fun I : Interval =>
      ⟨decide (candidate.value.1 ≤ I.1 ∧ I.2 ≤ candidate.value.2), 7⟩) L
    ⟨if candidate.value.1 < candidate.value.2 ∧ size.value ≤ 4 * inside.value
      then some candidate.value else none, size.work + candidate.work + inside.work + 10⟩

@[simp] theorem centralInterval_value (L : List Interval) :
    (centralInterval L).value = Certificates.centralInterval L := by
  simp only [centralInterval, Certificates.centralInterval, length_value]
  split
  · rfl
  · simp only [centralCandidate_value, PrimitiveWork.count_value,
      ← List.countP_eq_length_filter, insideCount]
    rfl

theorem centralInterval_work (L : List Interval) :
    (centralInterval L).work ≤ 65 * (L.length + 1) ^ 2 := by
  have hc := centralCandidate_work L
  have hi := PrimitiveWork.count_work_le (fun I : Interval =>
    (⟨decide ((centralCandidate L).value.1 ≤ I.1 ∧ I.2 ≤ (centralCandidate L).value.2), 7⟩ :
      PrimitiveWork.Result Bool)) L 7 (fun _ _ => le_rfl)
  simp only [centralInterval, length_work]
  split <;> dsimp only <;> nlinarith

end SortingAdversary.Continuous.CertificateWork
