import SortingAdversary.Continuous.EnclosureWork
import SortingAdversary.Continuous.GraphWork
import SortingAdversary.Continuous.UniformStages

/-!
# Counted sparse repair scans

Paths are generated through measured outgoing-neighbor scans. Both the path
enumeration and lexicographic minimum are implemented here; a whole-path
comparison is charged for the list cells it examines. Degree choice counts
neighbors in the stored matrix and scans labels in their actual order.
-/

namespace SortingAdversary.Continuous.GraphScanWork

open SortingAdversary.Optimal GraphBalls
open EnclosureWork

variable {n : ℕ}

def filter {α : Type*} (f : α → PrimitiveWork.Result Bool) :
    List α → PrimitiveWork.Result (List α)
  | [] => ⟨[], 1⟩
  | x :: xs =>
    let test := f x
    let rest := filter f xs
    ⟨if test.value then x :: rest.value else rest.value, test.work + rest.work + 2⟩

@[simp] theorem filter_value {α : Type*} (f : α → PrimitiveWork.Result Bool) (xs : List α) :
    (filter f xs).value = xs.filter (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter, List.filter_cons, ih]

theorem filter_work {α : Type*} (f : α → PrimitiveWork.Result Bool) (xs : List α)
    (W : ℕ) (hw : ∀ x ∈ xs, (f x).work ≤ W) :
    (filter f xs).work ≤ xs.length * (W + 2) + 1 := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    have hx := hw x (by simp)
    have ht := ih (fun y hy => hw y (by simp [hy]))
    simp only [filter, List.length_cons, Nat.add_mul, one_mul]
    omega

def outgoing (D : StoredSystem n) (x : Fin n) : PrimitiveWork.Result (List (Fin n)) :=
  let result := filter (fun y => ⟨D.edge[x][y], 3⟩) (List.finRange n)
  ⟨result.value, result.work + 3 * n⟩

@[simp] theorem outgoing_value (D : StoredSystem n) (x : Fin n) :
    (outgoing D x).value = GraphPaths.outgoing D.system.edge x := by
  simp only [outgoing, filter_value, GraphPaths.outgoing]
  rfl

theorem outgoing_work (D : StoredSystem n) (x : Fin n) :
    (outgoing D x).work ≤ 8 * n + 1 := by
  have h := filter_work (fun y : Fin n => (⟨D.edge[x][y], 3⟩ : PrimitiveWork.Result Bool))
    (List.finRange n) 3 (fun _ _ => le_rfl)
  simp only [List.length_finRange] at h
  simp only [outgoing]
  omega

def pathsFrom (D : StoredSystem n) : ℕ → Fin n → PrimitiveWork.Result (List (List (Fin n)))
  | 0, _ => ⟨[[]], 2⟩
  | h + 1, x =>
    let adjacent := outgoing D x
    let result := flatMap (fun y =>
      let tails := pathsFrom D h y
      let entries := PrimitiveWork.map (fun p => ⟨y :: p, 1⟩) tails.value
      ⟨entries.value, tails.work + entries.work⟩) adjacent.value
    ⟨result.value, adjacent.work + result.work + 1⟩

@[simp] theorem pathsFrom_value (D : StoredSystem n) (h : ℕ) (x : Fin n) :
    (pathsFrom D h x).value = GraphPaths.pathsFrom D.system.edge h x := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    simp only [pathsFrom, outgoing_value, flatMap_value, PrimitiveWork.map_value,
      ih, GraphPaths.pathsFrom]

def fromBound (n d h : ℕ) : ℕ := 20 * (n + 1) * (h + 1) * (d + 1) ^ h

theorem pathsFrom_work (D : StoredSystem n) (d : ℕ)
    (hloop : ∀ x, D.system.edge x x = false)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ d) (h : ℕ) (x : Fin n) :
    (pathsFrom D h x).work ≤ fromBound n d h := by
  induction h generalizing x with
  | zero => simp [pathsFrom, fromBound]; omega
  | succ h ih =>
    let branch := fun y : Fin n =>
      let tails := pathsFrom D h y
      let entries := PrimitiveWork.map (fun p => ⟨y :: p, 1⟩) tails.value
      (⟨entries.value, tails.work + entries.work⟩ : PrimitiveWork.Result (List (List (Fin n))))
    have hlen (y : Fin n) : (pathsFrom D h y).value.length ≤ d ^ h := by
      rw [pathsFrom_value]
      exact GraphPaths.pathsFrom_length_le _ d hloop hdegree h y
    have hw : ∀ y ∈ (outgoing D x).value, (branch y).work ≤ fromBound n d h + 3 * d ^ h + 1 := by
      intro y _
      have hm := PrimitiveWork.map_work_le
        (fun p : List (Fin n) => (⟨y :: p, 1⟩ : PrimitiveWork.Result (List (Fin n))))
        (pathsFrom D h y).value 1 (fun _ _ => le_rfl)
      have hy := ih y
      have hh := hlen y
      dsimp only [branch]
      omega
    have hl : ∀ y ∈ (outgoing D x).value, (branch y).value.length ≤ d ^ h := by
      intro y _
      simpa only [branch, PrimitiveWork.map_value, List.length_map] using hlen y
    have hf := flatMap_work branch (outgoing D x).value (fromBound n d h + 3 * d ^ h + 1)
      (d ^ h) hw hl
    have hn : (outgoing D x).value.length ≤ d := by
      rw [outgoing_value]
      exact GraphPaths.outgoing_length_le _ d hloop hdegree x
    have hf' := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
    have ho := outgoing_work D x
    have hp : d ^ h ≤ (d + 1) ^ h := Nat.pow_le_pow_left (by omega) h
    have hpos : 1 ≤ (d + 1) ^ h := Nat.one_le_pow _ _ (by omega)
    change (outgoing D x).work + (flatMap branch (outgoing D x).value).work + 1 ≤ _
    have htail : fromBound n d h + 3 * d ^ h + 1 + d ^ h + 2 ≤
        (20 * (n + 1) * (h + 1) + 7) * (d + 1) ^ h := by
      unfold fromBound
      nlinarith
    have hf'' := hf'.trans (Nat.add_le_add_right (Nat.mul_le_mul_left d htail) 1)
    have hbase : 8 * n + 3 ≤ (8 * n + 3) * (d + 1) ^ h :=
      Nat.le_mul_of_pos_right _ hpos
    have halgebra : 8 * n + 3 + d * (20 * (n + 1) * (h + 1) + 7) ≤
        20 * (n + 1) * (h + 2) * (d + 1) := by
      nlinarith [Nat.zero_le (n * h), Nat.zero_le (n * d)]
    calc
      _ ≤ (8 * n + 3) * (d + 1) ^ h +
          d * ((20 * (n + 1) * (h + 1) + 7) * (d + 1) ^ h) := by omega
      _ = (8 * n + 3 + d * (20 * (n + 1) * (h + 1) + 7)) * (d + 1) ^ h := by ring
      _ ≤ (20 * (n + 1) * (h + 2) * (d + 1)) * (d + 1) ^ h :=
        Nat.mul_le_mul_right _ halgebra
      _ = fromBound n d (h + 1) := by unfold fromBound; rw [pow_succ]; ring

def paths (D : StoredSystem n) : ℕ → PrimitiveWork.Result (List (List (Fin n)))
  | 0 => ⟨[[]], 2⟩
  | h + 1 =>
    let result := flatMap (fun x =>
      let tails := pathsFrom D h x
      let entries := PrimitiveWork.map (fun p => ⟨x :: p, 1⟩) tails.value
      ⟨entries.value, tails.work + entries.work⟩) (List.finRange n)
    ⟨result.value, result.work + 3 * n + 1⟩

@[simp] theorem paths_value (D : StoredSystem n) (H : ℕ) :
    (paths D H).value = GraphPaths.paths D.system.edge H := by
  cases H <;> simp only [paths, flatMap_value, PrimitiveWork.map_value,
    pathsFrom_value, GraphPaths.paths]

theorem paths_work (D : StoredSystem n) (d : ℕ)
    (hloop : ∀ x, D.system.edge x x = false)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ d) (H : ℕ) :
    (paths D H).work ≤ 40 * (n + 1) ^ 2 * (H + 1) * (d + 1) ^ H := by
  cases H with
  | zero =>
    simp only [paths, Nat.zero_add, pow_zero, Nat.mul_one]
    have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  | succ h =>
    let branch := fun x : Fin n =>
      let tails := pathsFrom D h x
      let entries := PrimitiveWork.map (fun p => ⟨x :: p, 1⟩) tails.value
      (⟨entries.value, tails.work + entries.work⟩ : PrimitiveWork.Result (List (List (Fin n))))
    have hlen (x : Fin n) : (pathsFrom D h x).value.length ≤ d ^ h := by
      rw [pathsFrom_value]
      exact GraphPaths.pathsFrom_length_le _ d hloop hdegree h x
    have hw : ∀ x ∈ List.finRange n, (branch x).work ≤ fromBound n d h + 3 * d ^ h + 1 := by
      intro x _
      have hm := PrimitiveWork.map_work_le
        (fun p : List (Fin n) => (⟨x :: p, 1⟩ : PrimitiveWork.Result (List (Fin n))))
        (pathsFrom D h x).value 1 (fun _ _ => le_rfl)
      have ht := pathsFrom_work D d hloop hdegree h x
      have hh := hlen x
      dsimp only [branch]
      omega
    have hl : ∀ x ∈ List.finRange n, (branch x).value.length ≤ d ^ h := by
      intro x _
      simpa only [branch, PrimitiveWork.map_value, List.length_map] using hlen x
    have hf := flatMap_work branch (List.finRange n) (fromBound n d h + 3 * d ^ h + 1)
      (d ^ h) hw hl
    simp only [List.length_finRange] at hf
    have hp : d ^ h ≤ (d + 1) ^ h := Nat.pow_le_pow_left (by omega) h
    have hpos : 1 ≤ (d + 1) ^ h := Nat.one_le_pow _ _ (by omega)
    change (flatMap branch (List.finRange n)).work + 3 * n + 1 ≤ _
    have htail : fromBound n d h + 3 * d ^ h + 1 + d ^ h + 2 ≤
        (20 * (n + 1) * (h + 1) + 7) * (d + 1) ^ h := by
      unfold fromBound
      nlinarith
    have hf' := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_left n htail) 1)
    have hbase : 3 * n + 2 ≤ (3 * n + 2) * (d + 1) ^ h :=
      Nat.le_mul_of_pos_right _ hpos
    have halgebra : 3 * n + 2 + n * (20 * (n + 1) * (h + 1) + 7) ≤
        40 * (n + 1) ^ 2 * (h + 2) := by
      nlinarith [Nat.zero_le (n ^ 2 * h), Nat.zero_le (n * h), Nat.zero_le (n ^ 2)]
    calc
      _ ≤ (3 * n + 2) * (d + 1) ^ h +
          n * ((20 * (n + 1) * (h + 1) + 7) * (d + 1) ^ h) := by omega
      _ = (3 * n + 2 + n * (20 * (n + 1) * (h + 1) + 7)) * (d + 1) ^ h := by ring
      _ ≤ (40 * (n + 1) ^ 2 * (h + 2)) * (d + 1) ^ h :=
        Nat.mul_le_mul_right _ halgebra
      _ ≤ 40 * (n + 1) ^ 2 * (h + 1 + 1) * (d + 1) ^ (h + 1) := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

def lexLE : List (Fin n) → List (Fin n) → PrimitiveWork.Result Bool
  | [], _ => ⟨true, 1⟩
  | _ :: _, [] => ⟨false, 1⟩
  | a :: as, b :: bs =>
    let tail := lexLE as bs
    ⟨decide (a < b) || (decide (a = b) && tail.value), tail.work + 5⟩

@[simp] theorem lexLE_value (xs ys : List (Fin n)) :
    (lexLE xs ys).value = decide (xs ≤ ys) := by
  induction xs generalizing ys with
  | nil =>
    change true = decide ([] ≤ ys)
    symm
    apply decide_eq_true
    cases ys with
    | nil => exact le_rfl
    | cons y ys => exact le_of_lt (List.Lex.nil (r := fun a b : Fin n => a < b))
  | cons a as ih =>
    cases ys with
    | nil => simp [lexLE]
    | cons b bs =>
      simp only [lexLE, ih]
      rw [← Bool.decide_and, ← Bool.decide_or]
      rw [decide_eq_decide]
      symm
      simp only [le_iff_lt_or_eq]
      change (List.Lex (fun x y : Fin n => x < y) (a :: as) (b :: bs) ∨ a :: as = b :: bs) ↔
        a < b ∨ a = b ∧ (List.Lex (fun x y : Fin n => x < y) as bs ∨ as = bs)
      simp only [List.cons_lex_cons_iff, List.cons.injEq]
      tauto

theorem lexLE_work (xs ys : List (Fin n)) : (lexLE xs ys).work ≤ 5 * xs.length + 1 := by
  induction xs generalizing ys with
  | nil => simp [lexLE]
  | cons a as ih => cases ys <;> simp only [lexLE, List.length_cons] <;> grind

def minimum : List (List (Fin n)) → PrimitiveWork.Result (Option (List (Fin n)))
  | [] => ⟨none, 1⟩
  | x :: xs =>
    let tail := minimum xs
    match tail.value with
    | none => ⟨some x, tail.work + 2⟩
    | some y =>
      let test := lexLE x y
      ⟨some (if test.value then x else y), tail.work + test.work + 3⟩

@[simp] theorem minimum_value (xs : List (List (Fin n))) :
    (minimum xs).value = xs.min? := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [minimum, ih, List.min?_cons]
    cases xs.min? <;> simp [lexLE_value, min_def]

theorem minimum_work (xs : List (List (Fin n))) (H : ℕ)
    (hH : ∀ p ∈ xs, p.length ≤ H) :
    (minimum xs).work ≤ xs.length * (5 * H + 4) + 1 := by
  induction xs with
  | nil => simp [minimum]
  | cons x xs ih =>
    have hx := hH x (by simp)
    have ht := ih (fun p hp => hH p (by simp [hp]))
    simp only [minimum, List.length_cons]
    split
    · dsimp only; nlinarith
    · rename_i y hy
      have hc := lexLE_work x y
      dsimp only
      nlinarith

def firstPath (D : StoredSystem n) (H : ℕ) : PrimitiveWork.Result (Option (List (Fin n))) :=
  let candidates := paths D H
  let result := minimum candidates.value
  ⟨result.value, candidates.work + result.work⟩

@[simp] theorem firstPath_value (D : StoredSystem n) (H : ℕ) :
    (firstPath D H).value = GraphPaths.firstPath D.system.edge H := by
  simp only [firstPath, minimum_value, paths_value, GraphPaths.firstPath]

theorem firstPath_work (D : StoredSystem n) (d : ℕ)
    (hloop : ∀ x, D.system.edge x x = false)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ d) (H : ℕ) :
    (firstPath D H).work ≤ 50 * (n + 1) ^ 2 * (H + 1) * (d + 1) ^ H := by
  have hp := paths_work D d hloop hdegree H
  have hm := minimum_work (paths D H).value H (by
    intro p hp
    rw [paths_value] at hp
    exact ((GraphPaths.mem_paths D.system.edge H p).mp hp).1.le)
  have hlen : (paths D H).value.length ≤ (n + 1) * (d + 1) ^ H := by
    rw [paths_value]
    cases H with
    | zero => simp [GraphPaths.paths]
    | succ h =>
      have hh := GraphPaths.paths_length_le D.system.edge d hloop hdegree h
      exact hh.trans (Nat.mul_le_mul (by omega) (by
        calc
          d ^ h ≤ (d + 1) ^ h := Nat.pow_le_pow_left (by omega) h
          _ ≤ (d + 1) ^ (h + 1) := Nat.pow_le_pow_right (by omega) (by omega)))
  have hm' := hm.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hpos : 1 ≤ (d + 1) ^ H := Nat.one_le_pow _ _ (by omega)
  simp only [firstPath]
  nlinarith [Nat.zero_le (n ^ 2 * H * (d + 1) ^ H)]

def degree (D : StoredSystem n) (x : Fin n) : PrimitiveWork.Result ℕ :=
  let result := PrimitiveWork.count (fun y : Fin n =>
    ⟨decide (y ≠ x) && (D.edge[x][y] || D.edge[y][x]), 7⟩) (List.finRange n)
  ⟨result.value, result.work + 3 * n⟩

@[simp] theorem degree_value (D : StoredSystem n) (x : Fin n) :
    (degree D x).value = (neighbors D.system.edge x).card := by
  simp only [degree, PrimitiveWork.count_value]
  have hn := (List.nodup_finRange n).filter (fun y : Fin n =>
    decide (y ≠ x) && (D.edge[x][y] || D.edge[y][x]))
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext y
  rw [List.mem_toFinset, List.mem_filter, mem_neighbors]
  simp [StoredSystem.system, SparseClosure.lookup]

theorem degree_work (D : StoredSystem n) (x : Fin n) :
    (degree D x).work ≤ 13 * n + 1 := by
  have h := PrimitiveWork.count_work_le (fun y : Fin n =>
    (⟨decide (y ≠ x) && (D.edge[x][y] || D.edge[y][x]), 7⟩ : PrimitiveWork.Result Bool))
    (List.finRange n) 7 (fun _ _ => le_rfl)
  simp only [List.length_finRange] at h
  simp only [degree]
  omega

def degreeChoice (D : StoredSystem n) (k : ℕ) : PrimitiveWork.Result (Option (Fin n)) :=
  let result := PrimitiveWork.find (fun x =>
    let count := degree D x
    ⟨decide (count.value = k), count.work + 1⟩) (List.finRange n)
  ⟨result.value, result.work + 3 * n⟩

@[simp] theorem degreeChoice_value (D : StoredSystem n) (k : ℕ) :
    (degreeChoice D k).value = (List.finRange n).find?
      (fun x => decide ((neighbors D.system.edge x).card = k)) := by
  simp only [degreeChoice, PrimitiveWork.find_value, degree_value]

theorem degreeChoice_work (D : StoredSystem n) (k : ℕ) :
    (degreeChoice D k).work ≤ 20 * (n + 1) ^ 2 := by
  have hf := PrimitiveWork.find_work_le (fun x =>
    (⟨decide ((degree D x).value = k), (degree D x).work + 1⟩ : PrimitiveWork.Result Bool))
    (List.finRange n) (13 * n + 2) (fun x _ => by dsimp only; have := degree_work D x; omega)
  simp only [List.length_finRange] at hf
  simp only [degreeChoice]
  nlinarith

/-- The two parameter-dependent factors of the real path enumeration are
bounded before combining them with the ambient matrix scans. -/
theorem firstPath_work_bounded (D : StoredSystem n) (d H cap : ℕ)
    (hloop : ∀ x, D.system.edge x x = false)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ d)
    (hH : H ≤ cap) (hpower : (d + 1) ^ H ≤ cap) :
    (firstPath D H).work ≤ 50 * (n + 1) ^ 2 * (cap + 1) ^ 2 := by
  apply (firstPath_work D d hloop hdegree H).trans
  calc
    _ ≤ 50 * (n + 1) ^ 2 * (cap + 1) * (cap + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hH 1)) (by omega)
    _ = _ := by ring

/-- Admission of the actual stage expression bounds the exponential path
search as well as the finite averaging calculation. -/
theorem firstPath_work_admitted (D : StoredSystem n) (j cap : ℕ)
    (hcap : UniformStages.Recipe.budget.need j ≤ cap)
    (hloop : ∀ x, D.system.edge x x = false)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ UniformStages.degree j) :
    (firstPath D (2 ^ UniformStages.degree j)).work ≤
      50 * (n + 1) ^ 2 * (cap + 1) ^ 2 := by
  have hs := UniformStages.admitted_scalar_bounds j cap hcap
  have hH : 2 ^ UniformStages.degree j ≤ ArbitraryLabels.pathHeight (UniformStages.degree j) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  apply firstPath_work_bounded D (UniformStages.degree j) _ cap hloop hdegree (hH.trans hs.2.1)
  apply le_trans ?_ hs.2.2.1
  unfold EnclosureParameters.neighborhoodBound
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem firstPath_work_admitted_input (D : StoredSystem n) (j cap : ℕ)
    (hcap : UniformStages.Recipe.budget.need j ≤ cap) (hinput : cap ≤ n)
    (hloop : ∀ x, D.system.edge x x = false)
    (hdegree : ∀ x, (neighbors D.system.edge x).card ≤ UniformStages.degree j) :
    (firstPath D (2 ^ UniformStages.degree j)).work ≤ 50 * (n + 1) ^ 4 := by
  apply (firstPath_work_admitted D j cap hcap hloop hdegree).trans
  calc
    _ ≤ 50 * (n + 1) ^ 2 * (n + 1) ^ 2 := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by ring

end SortingAdversary.Continuous.GraphScanWork
