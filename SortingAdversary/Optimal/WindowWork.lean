import SortingAdversary.Optimal.FiniteLoopWork
import SortingAdversary.Optimal.WeakMaps
import SortingAdversary.Optimal.CutNormalization

/-!
# Primitive work of propagated numerical windows

Each effective endpoint is a single finite maximum/minimum scan. The row and
primitive-wall getters have explicit measured costs. Their functional
representation is therefore paid for at every actual lookup. The finite
carrier list is generated once per scan and no map assignments are enumerated.
-/

namespace SortingAdversary.Optimal.WindowWork

open PrimitiveWork WeakMaps WeakMaps.WeakSystem

section Fold

variable {α β : Type*} [DecidableEq α] [SemilatticeSup β] [OrderBot β]

def supremum (f : α → Result β) : List α → Result β
  | [] => ⟨⊥, 1⟩
  | x :: xs =>
      let head := f x
      let tail := supremum f xs
      ⟨head.value ⊔ tail.value, head.work + tail.work + 3⟩

@[simp] theorem supremum_value (f : α → Result β) (xs : List α) :
    (supremum f xs).value = xs.toFinset.sup (fun x => (f x).value) := by
  induction xs with
  | nil => simp [supremum]
  | cons x xs ih => simp only [supremum, List.toFinset_cons, Finset.sup_insert, ih]

omit [DecidableEq α] in
theorem supremum_work_le (f : α → Result β) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (supremum f xs).work ≤ xs.length * (bound + 3) + 1 := by
  induction xs with
  | nil => simp [supremum]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [supremum, List.length_cons, Nat.add_mul, one_mul]
    omega

end Fold

section Infimum

variable {α β : Type*} [DecidableEq α] [SemilatticeInf β] [OrderTop β]

def infimum (f : α → Result β) : List α → Result β
  | [] => ⟨⊤, 1⟩
  | x :: xs =>
      let head := f x
      let tail := infimum f xs
      ⟨head.value ⊓ tail.value, head.work + tail.work + 3⟩

@[simp] theorem infimum_value (f : α → Result β) (xs : List α) :
    (infimum f xs).value = xs.toFinset.inf (fun x => (f x).value) := by
  induction xs with
  | nil => simp [infimum]
  | cons x xs ih => simp only [infimum, List.toFinset_cons, Finset.inf_insert, ih]

omit [DecidableEq α] in
theorem infimum_work_le (f : α → Result β) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (infimum f xs).work ≤ xs.length * (bound + 3) + 1 := by
  induction xs with
  | nil => simp [infimum]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [infimum, List.length_cons, Nat.add_mul, one_mul]
    omega

end Infimum

variable {n K : ℕ}

structure Input (n K : ℕ) where
  edge : Fin n → Fin n → Result Bool
  lower : Fin n → Result (Fin (K + 1))
  upper : Fin n → Result (Fin (K + 1))

def Input.system (input : Input n K) : WeakSystem (Fin n) (K + 1) where
  edge x y := (input.edge x y).value
  lower x := (input.lower x).value
  upper x := (input.upper x).value

def lowerTerm (input : Input n K) (v u : Fin n) : Result (Fin (K + 1)) :=
  let row := input.edge u v
  if row.value then
    let wall := input.lower u
    ⟨wall.value, row.work + wall.work + 1⟩
  else ⟨⊥, row.work + 1⟩

def upperTerm (input : Input n K) (v u : Fin n) : Result (Fin (K + 1)) :=
  let row := input.edge v u
  if row.value then
    let wall := input.upper u
    ⟨wall.value, row.work + wall.work + 1⟩
  else ⟨⊤, row.work + 1⟩

@[simp] theorem lowerTerm_value (input : Input n K) (v u : Fin n) :
    (lowerTerm input v u).value =
      if input.system.edge u v = true then input.system.lower u else ⊥ := by
  by_cases h : (input.edge u v).value = true <;> simp [lowerTerm, Input.system, h]

@[simp] theorem upperTerm_value (input : Input n K) (v u : Fin n) :
    (upperTerm input v u).value =
      if input.system.edge v u = true then input.system.upper u else ⊤ := by
  by_cases h : (input.edge v u).value = true <;> simp [upperTerm, Input.system, h]

theorem lowerTerm_work_le (input : Input n K) (v u : Fin n) (row wall : ℕ)
    (hr : (input.edge u v).work ≤ row) (hw : (input.lower u).work ≤ wall) :
    (lowerTerm input v u).work ≤ row + wall + 1 := by
  simp only [lowerTerm]
  split <;> dsimp only <;> omega

theorem upperTerm_work_le (input : Input n K) (v u : Fin n) (row wall : ℕ)
    (hr : (input.edge v u).work ≤ row) (hw : (input.upper u).work ≤ wall) :
    (upperTerm input v u).work ≤ row + wall + 1 := by
  simp only [upperTerm]
  split <;> dsimp only <;> omega

def effectiveLower (input : Input n K) (v : Fin n) : Result (Fin (K + 1)) :=
  let domain := FiniteLoopWork.indices n
  let answer := supremum (lowerTerm input v) domain.value
  ⟨answer.value, domain.work + answer.work⟩

def effectiveUpper (input : Input n K) (v : Fin n) : Result (Fin (K + 1)) :=
  let domain := FiniteLoopWork.indices n
  let answer := infimum (upperTerm input v) domain.value
  ⟨answer.value, domain.work + answer.work⟩

private theorem finRange_toFinset (n : ℕ) : (List.finRange n).toFinset = Finset.univ := by
  ext x
  simp

@[simp] theorem effectiveLower_value (input : Input n K) (v : Fin n) :
    (effectiveLower input v).value = input.system.effectiveLower v := by
  simp only [effectiveLower, FiniteLoopWork.indices, supremum_value, finRange_toFinset,
    lowerTerm_value, WeakSystem.effectiveLower]

@[simp] theorem effectiveUpper_value (input : Input n K) (v : Fin n) :
    (effectiveUpper input v).value = input.system.effectiveUpper v := by
  simp only [effectiveUpper, FiniteLoopWork.indices, infimum_value, finRange_toFinset,
    upperTerm_value, WeakSystem.effectiveUpper]

def endpointWorkBound (n row wall : ℕ) : ℕ := 3 * n + n * (row + wall + 4) + 2

theorem effectiveLower_work_le (input : Input n K) (v : Fin n) (row wall : ℕ)
    (hr : ∀ u, (input.edge u v).work ≤ row) (hw : ∀ u, (input.lower u).work ≤ wall) :
    (effectiveLower input v).work ≤ endpointWorkBound n row wall := by
  have hf := supremum_work_le (lowerTerm input v) (List.finRange n) (row + wall + 1)
    (fun u _ => lowerTerm_work_le input v u row wall (hr u) (hw u))
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at hf
  change (3 * n + 1) + (supremum (lowerTerm input v) (List.finRange n)).work ≤ _
  unfold endpointWorkBound
  simp only [Nat.add_assoc]
  omega

theorem effectiveUpper_work_le (input : Input n K) (v : Fin n) (row wall : ℕ)
    (hr : ∀ u, (input.edge v u).work ≤ row) (hw : ∀ u, (input.upper u).work ≤ wall) :
    (effectiveUpper input v).work ≤ endpointWorkBound n row wall := by
  have hf := infimum_work_le
    (upperTerm input v) (List.finRange n) (row + wall + 1)
    (fun u _ => upperTerm_work_le input v u row wall (hr u) (hw u))
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at hf
  change (3 * n + 1) + (infimum
    (upperTerm input v) (List.finRange n)).work ≤ _
  unfold endpointWorkBound
  simp only [Nat.add_assoc]
  omega

def width (input : Input n K) (v : Fin n) : Result ℕ :=
  let lower := effectiveLower input v
  let upper := effectiveUpper input v
  ⟨upper.value.val + 1 - lower.value.val, lower.work + upper.work + 2⟩

@[simp] theorem width_value (input : Input n K) (v : Fin n) :
    (width input v).value = CutNormalization.width input.system v := by
  simp only [width, effectiveLower_value, effectiveUpper_value, CutNormalization.width]

theorem width_work_le (input : Input n K) (v : Fin n) (row wall : ℕ)
    (hr : ∀ u w, (input.edge u w).work ≤ row)
    (hl : ∀ u, (input.lower u).work ≤ wall) (hu : ∀ u, (input.upper u).work ≤ wall) :
    (width input v).work ≤ 2 * endpointWorkBound n row wall + 2 := by
  have hL := effectiveLower_work_le input v row wall (fun u => hr u v) hl
  have hU := effectiveUpper_work_le input v row wall (hr v) hu
  change (effectiveLower input v).work + (effectiveUpper input v).work + 2 ≤ _
  omega

end SortingAdversary.Optimal.WindowWork
