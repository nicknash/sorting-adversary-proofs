import SortingAdversary.Continuous.Precision
import SortingAdversary.Optimal.PrimitiveWork
import SortingAdversary.Optimal.SparseClosure

/-!
# Counted exact endpoint calculations

The executable refinement of the endpoint kernel uses stored vectors and a
stored Boolean matrix. Max/min folds, neighbor scans, rational arithmetic and
vector construction all carry explicit primitive-operation charges. Values
are proved equal to the semantic `update` and `fullSteps`; counters are not
assigned from an external running-time claim. The rational operations are
word operations here, with operand precision supplied by `Precision`.
-/

namespace SortingAdversary.Continuous.EnclosureWork

open FiniteAveraging
open SortingAdversary.Optimal
open scoped BigOperators

variable {n : ℕ}

structure StoredSystem (n : ℕ) where
  lower : Vector ℚ n
  upper : Vector ℚ n
  edge : SparseClosure.Table n

def StoredSystem.system (D : StoredSystem n) : System (Fin n) ℚ :=
  ⟨fun x => D.lower[x], fun x => D.upper[x], SparseClosure.lookup D.edge⟩

def values (Y : Vector ℚ n) : Fin n → ℚ := fun x => Y[x]

private def combine (op : ℚ → ℚ → ℚ) (a b : PrimitiveWork.Result ℚ) : PrimitiveWork.Result ℚ :=
  ⟨op a.value b.value, a.work + b.work + 3⟩

private instance combine_comm (op : ℚ → ℚ → ℚ) [Std.Commutative op] :
    Std.Commutative (combine op) := ⟨by
  intro a b
  cases a with
  | mk a ac =>
    cases b with
    | mk b bc =>
      simp only [combine]
      congr 1
      · exact Std.Commutative.comm a b
      · omega⟩

private instance combine_assoc (op : ℚ → ℚ → ℚ) [Std.Associative op] :
    Std.Associative (combine op) := ⟨by
  intro a b c
  cases a with
  | mk a ac =>
    cases b with
    | mk b bc =>
      cases c with
      | mk c cc =>
        simp only [combine]
        congr 1
        · exact Std.Associative.assoc a b c
        · omega⟩

private theorem fold_value (op : ℚ → ℚ → ℚ) [Std.Commutative op] [Std.Associative op]
    (A : Finset (Fin n)) (base : PrimitiveWork.Result ℚ) (f : Fin n → PrimitiveWork.Result ℚ) :
    (A.fold (combine op) base f).value = A.fold op base.value (fun x => (f x).value) :=
  (Finset.fold_hom (m := PrimitiveWork.Result.value) (fun _ _ => rfl)).symm

private theorem fold_work (op : ℚ → ℚ → ℚ) [Std.Commutative op] [Std.Associative op]
    (A : Finset (Fin n)) (base : PrimitiveWork.Result ℚ) (f : Fin n → PrimitiveWork.Result ℚ) :
    (A.fold (combine op) base f).work = base.work + (∑ x ∈ A, (f x).work) + 3 * A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x A hx ih =>
    rw [Finset.fold_insert hx, Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
    change (f x).work + (A.fold (combine op) base f).work + 3 = _
    rw [ih]
    omega

def conditionalLower (D : StoredSystem n) (x : Fin n) (Y : Vector ℚ n) : PrimitiveWork.Result ℚ :=
  let neighbors := Finset.univ.filter (fun y : Fin n => D.edge[y][x] = true)
  let folded := neighbors.fold (combine max) ⟨D.lower[x], 1⟩ (fun y => ⟨Y[y], 1⟩)
  ⟨folded.value, 5 * n + folded.work⟩

def conditionalUpper (D : StoredSystem n) (x : Fin n) (Y : Vector ℚ n) : PrimitiveWork.Result ℚ :=
  let neighbors := Finset.univ.filter (fun y : Fin n => D.edge[x][y] = true)
  let folded := neighbors.fold (combine min) ⟨D.upper[x], 1⟩ (fun y => ⟨Y[y], 1⟩)
  ⟨folded.value, 5 * n + folded.work⟩

theorem conditionalLower_value (D : StoredSystem n) (x : Fin n) (Y : Vector ℚ n) :
    (conditionalLower D x Y).value = FiniteAveraging.conditionalLower D.system x (values Y) := by
  simp only [conditionalLower, fold_value]
  rfl

theorem conditionalUpper_value (D : StoredSystem n) (x : Fin n) (Y : Vector ℚ n) :
    (conditionalUpper D x Y).value = FiniteAveraging.conditionalUpper D.system x (values Y) := by
  simp only [conditionalUpper, fold_value]
  rfl

theorem conditionalLower_work (D : StoredSystem n) (x : Fin n) (Y : Vector ℚ n) :
    (conditionalLower D x Y).work ≤ 9 * n + 1 := by
  have hn : (Finset.univ.filter (fun y : Fin n => D.edge[y][x] = true)).card ≤ n := by
    simpa using Finset.card_le_univ (Finset.univ.filter (fun y : Fin n => D.edge[y][x] = true))
  simp only [conditionalLower, fold_work, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
  omega

theorem conditionalUpper_work (D : StoredSystem n) (x : Fin n) (Y : Vector ℚ n) :
    (conditionalUpper D x Y).work ≤ 9 * n + 1 := by
  have hn : (Finset.univ.filter (fun y : Fin n => D.edge[x][y] = true)).card ≤ n := by
    simpa using Finset.card_le_univ (Finset.univ.filter (fun y : Fin n => D.edge[x][y] = true))
  simp only [conditionalUpper, fold_work, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
  omega

/-- Both conditional bounds are evaluated once before the new vector is
constructed. Twelve arithmetic/read operations cover the exact affine digit. -/
def update (D : StoredSystem n) (S : ℕ) (j : Fin S) (x : Fin n) (Y : Vector ℚ n) :
    PrimitiveWork.Result (Vector ℚ n) :=
  let lower := conditionalLower D x Y
  let upper := conditionalUpper D x Y
  let next := digit S j Y[x] lower.value upper.value
  let stored := PrimitiveWork.vector (fun y => ⟨if y = x then next else Y[y], 3⟩)
  ⟨stored.value, lower.work + upper.work + 12 + stored.work⟩

theorem update_value (D : StoredSystem n) (S : ℕ) (j : Fin S) (x : Fin n) (Y : Vector ℚ n) :
    values (update D S j x Y).value = FiniteAveraging.update D.system S j x (values Y) := by
  funext y
  simp only [values, update, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn,
    conditionalLower_value, conditionalUpper_value, FiniteAveraging.update]
  by_cases hy : y = x <;> simp [hy, Function.update, values]

theorem update_work (D : StoredSystem n) (S : ℕ) (j : Fin S) (x : Fin n) (Y : Vector ℚ n) :
    (update D S j x Y).work ≤ 30 * (n + 1) := by
  have hl := conditionalLower_work D x Y
  have hu := conditionalUpper_work D x Y
  have hv := PrimitiveWork.vector_work_le
    (fun y => (⟨if y = x then digit S j Y[x] (conditionalLower D x Y).value
      (conditionalUpper D x Y).value else Y[y], 3⟩ : PrimitiveWork.Result ℚ)) 3 (fun _ => le_rfl)
  simp only [update]
  omega

def fullSteps (D : StoredSystem n) (S : ℕ) : List (Fin n × Fin S) → Vector ℚ n →
    PrimitiveWork.Result (Vector ℚ n)
  | [], Y => ⟨Y, 1⟩
  | (x, j) :: steps, Y =>
    let next := update D S j x Y
    let rest := fullSteps D S steps next.value
    ⟨rest.value, next.work + rest.work + 1⟩

theorem fullSteps_value (D : StoredSystem n) (S : ℕ) (steps : List (Fin n × Fin S))
    (Y : Vector ℚ n) : values (fullSteps D S steps Y).value =
      FiniteAveraging.fullSteps D.system S steps (values Y) := by
  induction steps generalizing Y with
  | nil => rfl
  | cons step steps ih =>
    obtain ⟨x, j⟩ := step
    simp only [fullSteps, ih, update_value, FiniteAveraging.fullSteps, List.foldl_cons]

theorem fullSteps_work (D : StoredSystem n) (S : ℕ) (steps : List (Fin n × Fin S))
    (Y : Vector ℚ n) :
    (fullSteps D S steps Y).work ≤ steps.length * (30 * (n + 1) + 1) + 1 := by
  induction steps generalizing Y with
  | nil => simp [fullSteps]
  | cons step steps ih =>
    obtain ⟨x, j⟩ := step
    have hu := update_work D S j x Y
    have ht := ih (update D S j x Y).value
    simp only [fullSteps, List.length_cons, Nat.add_mul, one_mul]
    omega

/-- Counted concatenation charges each copied list cell. -/
def flatMap {α β : Type*} (f : α → PrimitiveWork.Result (List β)) :
    List α → PrimitiveWork.Result (List β)
  | [] => ⟨[], 1⟩
  | x :: xs =>
    let head := f x
    let tail := flatMap f xs
    ⟨head.value ++ tail.value, head.work + tail.work + head.value.length + 2⟩

theorem flatMap_value {α β : Type*} (f : α → PrimitiveWork.Result (List β)) (xs : List α) :
    (flatMap f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [flatMap, List.flatMap_cons, ih]

theorem flatMap_work {α β : Type*} (f : α → PrimitiveWork.Result (List β)) (xs : List α)
    (W L : ℕ) (hW : ∀ x ∈ xs, (f x).work ≤ W) (hL : ∀ x ∈ xs, (f x).value.length ≤ L) :
    (flatMap f xs).work ≤ xs.length * (W + L + 2) + 1 := by
  induction xs with
  | nil => simp [flatMap]
  | cons x xs ih =>
    have hw := hW x (by simp)
    have hl := hL x (by simp)
    have ht := ih (fun y hy => hW y (by simp [hy])) (fun y hy => hL y (by simp [hy]))
    simp only [flatMap, List.length_cons, Nat.add_mul, one_mul]
    omega

/-- A digit word is a concrete list, with its length in the type. It does
not carry an arbitrary function whose evaluation cost could be hidden. -/
inductive Word (S : ℕ) : ℕ → Type
  | nil : Word S 0
  | cons {m : ℕ} (digit : Fin S) (tail : Word S m) : Word S (m + 1)

def Word.eval {S : ℕ} : {m : ℕ} → Word S m → Fin m → Fin S
  | 0, .nil => Fin.elim0
  | _ + 1, .cons j tail => Fin.cons j tail.eval

def words (S : ℕ) : (m : ℕ) → PrimitiveWork.Result (List (Word S m))
  | 0 => ⟨[.nil], 1⟩
  | m + 1 =>
    let tails := words S m
    let branches := flatMap (fun j => PrimitiveWork.map
      (fun w => ⟨Word.cons j w, 1⟩) tails.value) (List.finRange S)
    ⟨branches.value, tails.work + branches.work + 3 * S + 1⟩

theorem words_value (S m : ℕ) : (words S m).value.map Word.eval = FiniteAveraging.words S m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [words, flatMap_value, PrimitiveWork.map_value, List.map_flatMap,
      List.map_map, Function.comp_def, Word.eval, FiniteAveraging.words]
    congr 1
    funext j
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun ws : List (Fin m → Fin S) =>
        ws.map (fun f : Fin m → Fin S => (Fin.cons j f : Fin (m + 1) → Fin S))) ih

theorem words_length (S m : ℕ) : (words S m).value.length = S ^ m := by
  rw [← List.length_map (f := Word.eval), words_value, FiniteAveraging.words_length]

theorem words_work (S m : ℕ) (hS : 0 < S) :
    (words S m).work ≤ 20 * (m + 1) * S ^ m := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    let branch := fun j : Fin S => PrimitiveWork.map
      (fun w : Word S m => (⟨Word.cons j w, 1⟩ : PrimitiveWork.Result (Word S (m + 1))))
      (words S m).value
    have hw : ∀ j ∈ List.finRange S, (branch j).work ≤ 3 * S ^ m + 1 := by
      intro j _
      have hh := PrimitiveWork.map_work_le
        (fun w : Word S m => (⟨Word.cons j w, 1⟩ : PrimitiveWork.Result (Word S (m + 1))))
        (words S m).value 1 (fun _ _ => le_rfl)
      simpa only [branch, words_length, Nat.reduceAdd, Nat.mul_comm] using hh
    have hl : ∀ j ∈ List.finRange S, (branch j).value.length ≤ S ^ m := by
      intro j _
      simp only [branch, PrimitiveWork.map_value, List.length_map, words_length, le_refl]
    have hb := flatMap_work branch (List.finRange S) (3 * S ^ m + 1) (S ^ m) hw hl
    simp only [List.length_finRange] at hb
    have hN : 1 ≤ S ^ m := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hS.ne')
    have hNS : S ^ m ≤ S ^ m * S := Nat.le_mul_of_pos_right _ hS
    have hSN : S ≤ S ^ m * S := by nlinarith
    change (words S m).work + (flatMap branch (List.finRange S)).work + 3 * S + 1 ≤ _
    rw [pow_succ]
    nlinarith

def Word.assign {S : ℕ} : (schedule : List (Fin n)) → Word S schedule.length →
    PrimitiveWork.Result (List (Fin n × Fin S))
  | [], .nil => ⟨[], 1⟩
  | x :: xs, .cons j tail =>
    let rest := tail.assign xs
    ⟨(x, j) :: rest.value, rest.work + 3⟩

theorem Word.assign_value {S : ℕ} (schedule : List (Fin n)) (w : Word S schedule.length) :
    (w.assign schedule).value = assignedSteps S schedule w.eval := by
  induction schedule with
  | nil => cases w; rfl
  | cons x xs ih =>
    cases w with
    | cons j tail =>
      simp only [Word.assign, Word.eval, assignedSteps_cons, Fin.tail_cons, Fin.cons_zero, ih]

theorem Word.assign_length {S : ℕ} (schedule : List (Fin n)) (w : Word S schedule.length) :
    (w.assign schedule).value.length = schedule.length := by
  rw [w.assign_value, assignedSteps]
  simp

theorem Word.assign_work {S : ℕ} (schedule : List (Fin n)) (w : Word S schedule.length) :
    (w.assign schedule).work = 3 * schedule.length + 1 := by
  induction schedule with
  | nil => cases w; rfl
  | cons x xs ih =>
    cases w with
    | cons j tail => simp only [Word.assign, ih, List.length_cons]; omega

def endpoint (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n))
    (w : Word S schedule.length) (x : Fin n) : PrimitiveWork.Result (ℚ × ℚ) :=
  let steps := w.assign schedule
  let lower := fullSteps D S steps.value D.lower
  let upper := fullSteps D S steps.value D.upper
  ⟨(lower.value[x], upper.value[x]), steps.work + lower.work + upper.work + 2⟩

theorem endpoint_value (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n))
    (w : Word S schedule.length) (x : Fin n) :
    (endpoint D S schedule w x).value = endpointEntry D.system S schedule w.eval x := by
  have hl := congrFun (fullSteps_value D S (w.assign schedule).value D.lower) x
  have hu := congrFun (fullSteps_value D S (w.assign schedule).value D.upper) x
  unfold values at hl hu
  apply Prod.ext
  · simpa only [endpoint, endpointEntry, values, Word.assign_value, StoredSystem.system] using hl
  · simpa only [endpoint, endpointEntry, values, Word.assign_value, StoredSystem.system] using hu

def endpointBound (n m : ℕ) : ℕ := m * (60 * (n + 1) + 5) + 5

theorem endpoint_work (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n))
    (w : Word S schedule.length) (x : Fin n) :
    (endpoint D S schedule w x).work ≤ endpointBound n schedule.length := by
  have hl := fullSteps_work D S (w.assign schedule).value D.lower
  have hu := fullSteps_work D S (w.assign schedule).value D.upper
  rw [w.assign_length] at hl hu
  simp only [endpoint, Word.assign_work, endpointBound]
  nlinarith

def oneIntervals (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n)) (x : Fin n) :
    PrimitiveWork.Result (List (ℚ × ℚ)) :=
  let digits := words S schedule.length
  let entries := PrimitiveWork.map (fun w => endpoint D S schedule w x) digits.value
  ⟨entries.value, digits.work + entries.work⟩

theorem oneIntervals_value (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n)) (x : Fin n) :
    (oneIntervals D S schedule x).value = (enclose D.system S schedule).map (fun I => I x) := by
  simp only [oneIntervals, PrimitiveWork.map_value, endpoint_value, enclose, List.map_map,
    Function.comp_def]
  rw [← words_value S schedule.length, List.map_map]
  rfl

def twoIntervals (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n)) (x y : Fin n) :
    PrimitiveWork.Result (List Certificates.ComparisonIntervals) :=
  let digits := words S schedule.length
  let entries := PrimitiveWork.map (fun w =>
    let first := endpoint D S schedule w x
    let second := endpoint D S schedule w y
    ⟨(first.value, second.value), first.work + second.work + 1⟩) digits.value
  ⟨entries.value, digits.work + entries.work⟩

theorem twoIntervals_value (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n)) (x y : Fin n) :
    (twoIntervals D S schedule x y).value = LocalSelection.comparisonList D.system S schedule x y := by
  simp only [twoIntervals, PrimitiveWork.map_value, endpoint_value, LocalSelection.comparisonList,
    enclose, List.map_map, Function.comp_def]
  rw [← words_value S schedule.length, List.map_map]
  rfl

def thresholdIntervals (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n)) (x : Fin n) (c : ℚ) :
    PrimitiveWork.Result (List Certificates.ComparisonIntervals) :=
  let digits := words S schedule.length
  let entries := PrimitiveWork.map (fun w =>
    let first := endpoint D S schedule w x
    ⟨(first.value, (c, c)), first.work + 1⟩) digits.value
  ⟨entries.value, digits.work + entries.work⟩

theorem thresholdIntervals_value (D : StoredSystem n) (S : ℕ) (schedule : List (Fin n))
    (x : Fin n) (c : ℚ) :
    (thresholdIntervals D S schedule x c).value = LocalSelection.thresholdList D.system S schedule x c := by
  simp only [thresholdIntervals, PrimitiveWork.map_value, endpoint_value, LocalSelection.thresholdList,
    enclose, List.map_map, Function.comp_def]
  rw [← words_value S schedule.length, List.map_map]
  rfl

/-- Shared conservative bound for one-coordinate, threshold and two-coordinate
lists, including all digit-word construction and all endpoint calculations. -/
def listBound (n S m : ℕ) : ℕ :=
  20 * (m + 1) * S ^ m + S ^ m * (2 * endpointBound n m + 3) + 1

theorem oneIntervals_work (D : StoredSystem n) (S : ℕ) (hS : 0 < S)
    (schedule : List (Fin n)) (x : Fin n) :
    (oneIntervals D S schedule x).work ≤ listBound n S schedule.length := by
  have hw := words_work S schedule.length hS
  have hm := PrimitiveWork.map_work_le (fun w => endpoint D S schedule w x)
    (words S schedule.length).value (endpointBound n schedule.length)
    (fun w _ => endpoint_work D S schedule w x)
  rw [words_length] at hm
  simp only [oneIntervals, listBound]
  nlinarith

theorem twoIntervals_work (D : StoredSystem n) (S : ℕ) (hS : 0 < S)
    (schedule : List (Fin n)) (x y : Fin n) :
    (twoIntervals D S schedule x y).work ≤ listBound n S schedule.length := by
  have hw := words_work S schedule.length hS
  have hm := PrimitiveWork.map_work_le (fun w =>
    (⟨((endpoint D S schedule w x).value, (endpoint D S schedule w y).value),
      (endpoint D S schedule w x).work + (endpoint D S schedule w y).work + 1⟩ :
      PrimitiveWork.Result Certificates.ComparisonIntervals))
    (words S schedule.length).value (2 * endpointBound n schedule.length + 1)
    (fun w _ => by
      dsimp only
      have := endpoint_work D S schedule w x
      have := endpoint_work D S schedule w y
      omega)
  rw [words_length] at hm
  simp only [twoIntervals, listBound]
  simp only [Nat.add_assoc, Nat.reduceAdd] at hm ⊢
  omega

theorem thresholdIntervals_work (D : StoredSystem n) (S : ℕ) (hS : 0 < S)
    (schedule : List (Fin n)) (x : Fin n) (c : ℚ) :
    (thresholdIntervals D S schedule x c).work ≤ listBound n S schedule.length := by
  have hw := words_work S schedule.length hS
  have hm := PrimitiveWork.map_work_le (fun w =>
    (⟨((endpoint D S schedule w x).value, (c, c)), (endpoint D S schedule w x).work + 1⟩ :
      PrimitiveWork.Result Certificates.ComparisonIntervals))
    (words S schedule.length).value (endpointBound n schedule.length + 1)
    (fun w _ => Nat.add_le_add_right (endpoint_work D S schedule w x) 1)
  rw [words_length] at hm
  simp only [thresholdIntervals, listBound]
  nlinarith

end SortingAdversary.Continuous.EnclosureWork
