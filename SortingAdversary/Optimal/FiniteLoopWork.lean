import SortingAdversary.Optimal.PrimitiveWork

/-!
# Counted list and finite-carrier loops

These routines make list generation, filtering, concatenation and traversal
explicit in the primitive word model. Their value theorems permit their use
in place of the corresponding library loops in the adversary.
-/

namespace SortingAdversary.Optimal.FiniteLoopWork

open PrimitiveWork

def append : List α → List α → Result (List α)
  | [], ys => ⟨ys, 1⟩
  | x :: xs, ys =>
      let rest := append xs ys
      ⟨x :: rest.value, rest.work + 2⟩

@[simp] theorem append_value (xs ys : List α) : (append xs ys).value = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [append, List.cons_append, ih]

theorem append_work (xs ys : List α) : (append xs ys).work = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [append, List.length_cons, ih]; omega

def filter (f : α → Result Bool) : List α → Result (List α)
  | [] => ⟨[], 1⟩
  | x :: xs =>
      let head := f x
      let tail := filter f xs
      ⟨if head.value then x :: tail.value else tail.value, head.work + tail.work + 3⟩

@[simp] theorem filter_value (f : α → Result Bool) (xs : List α) :
    (filter f xs).value = xs.filter (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter, List.filter_cons, ih]

theorem filter_work_le (f : α → Result Bool) (xs : List α) (bound : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound) :
    (filter f xs).work ≤ xs.length * (bound + 3) + 1 := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [filter, List.length_cons, Nat.add_mul, one_mul]
    omega

def flatMap (f : α → Result (List β)) : List α → Result (List β)
  | [] => ⟨[], 1⟩
  | x :: xs =>
      let head := f x
      let tail := flatMap f xs
      let joined := append head.value tail.value
      ⟨joined.value, head.work + tail.work + joined.work + 1⟩

@[simp] theorem flatMap_value (f : α → Result (List β)) (xs : List α) :
    (flatMap f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [flatMap, List.flatMap_cons, append_value, ih]

theorem flatMap_work_le (f : α → Result (List β)) (xs : List α) (bound size : ℕ)
    (h : ∀ x ∈ xs, (f x).work ≤ bound)
    (hlen : ∀ x ∈ xs, (f x).value.length ≤ size) :
    (flatMap f xs).work ≤ xs.length * (bound + 2 * size + 2) + 1 := by
  induction xs with
  | nil => simp [flatMap]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hl := hlen x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      (fun y hy => hlen y (List.mem_cons_of_mem x hy))
    simp only [flatMap, append_work, List.length_cons, Nat.add_mul, one_mul]
    omega

def length : List α → Result ℕ
  | [] => ⟨0, 1⟩
  | _ :: xs =>
      let tail := length xs
      ⟨tail.value + 1, tail.work + 2⟩

@[simp] theorem length_value (xs : List α) : (length xs).value = xs.length := by
  induction xs <;> simp_all [length]

theorem length_work (xs : List α) : (length xs).work = 2 * xs.length + 1 := by
  induction xs <;> simp_all [length]
  omega

def foldl (f : α → β → Result α) : α → List β → Result α
  | current, [] => ⟨current, 1⟩
  | current, x :: xs =>
      let step := f current x
      let rest := foldl f step.value xs
      ⟨rest.value, step.work + rest.work + 1⟩

@[simp] theorem foldl_value (f : α → β → Result α) (initial : α) (xs : List β) :
    (foldl f initial xs).value = xs.foldl (fun current x => (f current x).value) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => simp only [foldl, List.foldl_cons, ih]

theorem foldl_work_le (f : α → β → Result α) (initial : α) (xs : List β) (bound : ℕ)
    (h : ∀ current x, x ∈ xs → (f current x).work ≤ bound) :
    (foldl f initial xs).work ≤ xs.length * (bound + 1) + 1 := by
  induction xs generalizing initial with
  | nil => simp [foldl]
  | cons x xs ih =>
    have hx := h initial x (List.mem_cons_self ..)
    have ht := ih (f initial x).value (fun current y hy => h current y (List.mem_cons_of_mem x hy))
    simp only [foldl, List.length_cons, Nat.add_mul, one_mul]
    omega

def indices (n : ℕ) : Result (List (Fin n)) := ⟨List.finRange n, 3 * n + 1⟩

def scan (f : Fin n → Result Bool) : Result (Option (Fin n)) :=
  let domain := indices n
  let answer := PrimitiveWork.find f domain.value
  ⟨answer.value, domain.work + answer.work⟩

@[simp] theorem scan_value (f : Fin n → Result Bool) :
    (scan f).value = (List.finRange n).find? (fun x => (f x).value) := by
  simp only [scan, indices, PrimitiveWork.find_value]

theorem scan_work_le (f : Fin n → Result Bool) (bound : ℕ)
    (h : ∀ x, (f x).work ≤ bound) :
    (scan f).work ≤ 3 * n + n * (bound + 2) + 2 := by
  have hf := PrimitiveWork.find_work_le f (List.finRange n) bound (fun x _ => h x)
  simp only [List.length_finRange] at hf
  change (3 * n + 1) + (PrimitiveWork.find f (List.finRange n)).work ≤ _
  omega

def pairs (n : ℕ) : Result (List (Fin n × Fin n)) :=
  let domain := indices n
  let answer := flatMap (fun x => PrimitiveWork.map (fun y => atom (x, y)) domain.value) domain.value
  ⟨answer.value, domain.work + answer.work⟩

@[simp] theorem pairs_value (n : ℕ) :
    (pairs n).value = (List.finRange n).flatMap
      (fun x => (List.finRange n).map (fun y => (x, y))) := by
  simp only [pairs, indices, flatMap_value, PrimitiveWork.map_value, atom]

theorem pairs_length (n : ℕ) : (pairs n).value.length = n * n := by
  simp [pairs_value, List.length_flatMap]

theorem pairs_work_le (n : ℕ) : (pairs n).work ≤ 3 * n + n * (5 * n + 3) + 2 := by
  have hm (x : Fin n) := PrimitiveWork.map_work_le (fun y => atom (x, y))
    (List.finRange n) 1 (fun _ _ => le_rfl)
  simp only [List.length_finRange, Nat.reduceAdd] at hm
  have hf := flatMap_work_le (fun x : Fin n => PrimitiveWork.map (fun y => atom (x, y))
    (List.finRange n)) (List.finRange n) (n * 3 + 1) n
    (fun x _ => hm x) (fun x _ => by simp only [PrimitiveWork.map_value, List.length_map, List.length_finRange]; exact le_rfl)
  simp only [List.length_finRange] at hf
  change (3 * n + 1) + (flatMap _ (List.finRange n)).work ≤ _
  have he : n * 3 + 1 + 2 * n + 2 = 5 * n + 3 := by omega
  rw [he] at hf
  dsimp only [indices] at *
  omega

def scanPairs (f : Fin n × Fin n → Result Bool) : Result (Option (Fin n × Fin n)) :=
  let domain := pairs n
  let answer := PrimitiveWork.find f domain.value
  ⟨answer.value, domain.work + answer.work⟩

@[simp] theorem scanPairs_value (f : Fin n × Fin n → Result Bool) :
    (scanPairs f).value = ((List.finRange n).flatMap
      (fun x => (List.finRange n).map (fun y => (x, y)))).find? (fun x => (f x).value) := by
  simp only [scanPairs, pairs_value, PrimitiveWork.find_value]

theorem scanPairs_work_le (f : Fin n × Fin n → Result Bool) (bound : ℕ)
    (h : ∀ x, (f x).work ≤ bound) :
    (scanPairs f).work ≤ 3 * n + n * (5 * n + 3) + n * n * (bound + 2) + 3 := by
  have hp := pairs_work_le n
  have hf := PrimitiveWork.find_work_le f (pairs n).value bound (fun x _ => h x)
  rw [pairs_length] at hf
  change (pairs n).work + (PrimitiveWork.find f (pairs n).value).work ≤ _
  omega

end SortingAdversary.Optimal.FiniteLoopWork
