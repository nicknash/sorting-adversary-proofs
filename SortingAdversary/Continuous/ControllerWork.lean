import SortingAdversary.Continuous.ControllerCorrect
import SortingAdversary.Optimal.PrimitiveWork

/-!
# Counted composition of the continuous controller

The component interface describes stored-data implementations and proves
their values equal to the semantic routines. This module executes those
components in the same branches and order as the actual controller. Action
lists are ghost traces: the implementation retains the resulting state and
answer, while the semantic controller supplies the proved accounting trace.

The work certificates concern individual calls along the actual execution.
They are composed below, rather than assigning a polynomial cost to an
opaque call of `compare`. Concrete stored-data components and reachable
operand bounds instantiate this interface separately.
-/

namespace SortingAdversary.Continuous.ControllerWork

open SortingAdversary.Optimal
open PrimitiveWork

variable {n k : ℕ}

structure Routines (n k : ℕ) where
  State : Type
  memory : State → Controller.Memory n
  attempt : State → Query n → PrimitiveWork.Result (LocalSelection.Result n)
  anchor : State → Fin n → PrimitiveWork.Result ℚ
  refine : State → Fin n → ℚ → PrimitiveWork.Result State
  record : State → Query n → Answer → PrimitiveWork.Result State
  firstPath : State → PrimitiveWork.Result (Option (List (Fin n)))
  degreeChoice : State → PrimitiveWork.Result (Option (Fin n))
  attempt_value : ∀ s q, (attempt s q).value = Controller.attempt (memory s) k q
  anchor_value : ∀ s x, (anchor s x).value = ArbitraryLabels.chooseAnchor (memory s).tree.system k x
  refine_value : ∀ s x c, memory (refine s x c).value =
    Controller.applyMove (memory s) (Controller.makeMove (memory s) x c)
  record_value : ∀ s q a, memory (record s q a).value = Controller.recorded (memory s) q a
  firstPath_value : ∀ s, (firstPath s).value = GraphPaths.firstPath (memory s).tree.system.edge (2 ^ k)
  degreeChoice_value : ∀ s, (degreeChoice s).value = Controller.degreeChoice (memory s) k

variable (R : Routines n k)

def resultView (r : Controller.Result n) : Controller.Memory n × Answer := (r.memory, r.answer)

def storedView (r : R.State × Answer) : Controller.Memory n × Answer := (R.memory r.1, r.2)

def selectLoop (q : Query n) : ℕ → R.State → PrimitiveWork.Result (Option (R.State × Answer))
  | 0, _ => ⟨none, 1⟩
  | fuel + 1, s =>
    let test := R.attempt s q
    match test.value with
    | .answer a => ⟨some (s, a), test.work + 2⟩
    | .refine x c =>
      let moved := R.refine s x c
      let tail := selectLoop q fuel moved.value
      ⟨tail.value, test.work + moved.work + tail.work + 3⟩

theorem selectLoop_value (q : Query n) (fuel : ℕ) (s : R.State) :
    (selectLoop R q fuel s).value.map (storedView R) =
      (Controller.selectLoop k q fuel (R.memory s)).map resultView := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases ha : Controller.attempt (R.memory s) k q with
    | answer a => simp only [selectLoop, R.attempt_value, ha, Controller.selectLoop, Option.map_some,
        storedView, resultView]
    | refine x c =>
      simp only [selectLoop, R.attempt_value, ha, Controller.selectLoop]
      rw [Option.map_map]
      have ht := ih (R.refine s x c).value
      rw [R.refine_value] at ht
      exact ht

def pathBatch : R.State → List (Fin n) → PrimitiveWork.Result R.State
  | s, [] => ⟨s, 1⟩
  | s, x :: xs =>
    let chosen := R.anchor s x
    let moved := R.refine s x chosen.value
    let tail := pathBatch moved.value xs
    ⟨tail.value, chosen.work + moved.work + tail.work + 3⟩

theorem pathBatch_value (s : R.State) (xs : List (Fin n)) :
    R.memory (pathBatch R s xs).value = (Controller.pathBatch k (R.memory s) xs).1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [pathBatch, ih, R.refine_value, R.anchor_value, Controller.pathBatch]

def repair (s : R.State) : PrimitiveWork.Result R.State :=
  let path := R.firstPath s
  match path.value with
  | some xs =>
    let fixed := pathBatch R s xs
    ⟨fixed.value, path.work + fixed.work + 2⟩
  | none =>
    let degree := R.degreeChoice s
    match degree.value with
    | none => ⟨s, path.work + degree.work + 3⟩
    | some x =>
      let chosen := R.anchor s x
      let moved := R.refine s x chosen.value
      ⟨moved.value, path.work + degree.work + chosen.work + moved.work + 5⟩

theorem repair_value (s : R.State) :
    R.memory (repair R s).value = (Controller.repair k (R.memory s)).1 := by
  cases hp : GraphPaths.firstPath (R.memory s).tree.system.edge (2 ^ k) with
  | some xs => simp only [repair, R.firstPath_value, hp, pathBatch_value, Controller.repair]
  | none =>
    cases hd : Controller.degreeChoice (R.memory s) k with
    | none => simp only [repair, R.firstPath_value, hp, R.degreeChoice_value, hd, Controller.repair]
    | some x => simp only [repair, R.firstPath_value, hp, R.degreeChoice_value, hd,
        R.refine_value, R.anchor_value, Controller.repair]

def compare (s : R.State) (q : Query n) : PrimitiveWork.Result (Option (R.State × Answer)) :=
  let selected := selectLoop R q 3 s
  match selected.value with
  | none => ⟨none, selected.work + 1⟩
  | some (t, a) =>
    let answered := R.record t q a
    let fixed := repair R answered.value
    ⟨some (fixed.value, a), selected.work + answered.work + fixed.work + 3⟩

theorem compare_value (s : R.State) (q : Query n) :
    (compare R s q).value.map (storedView R) =
      (Controller.compare k (R.memory s) q).map resultView := by
  have hv := selectLoop_value R q 3 s
  cases hs : (selectLoop R q 3 s).value with
  | none =>
    cases ht : Controller.selectLoop k q 3 (R.memory s) with
    | none => simp only [compare, hs, Option.map_none, Controller.compare, ht]
    | some r => simp [hs, ht] at hv
  | some z =>
    obtain ⟨t, a⟩ := z
    cases ht : Controller.selectLoop k q 3 (R.memory s) with
    | none => simp [hs, ht] at hv
    | some r =>
      have he : R.memory t = r.memory ∧ a = r.answer := by
        simpa only [hs, ht, Option.map_some, Option.some.injEq, storedView, resultView,
          Prod.mk.injEq] using hv
      simp only [compare, hs, Option.map_some, storedView, repair_value, R.record_value,
        he.1, he.2, Controller.compare, ht, resultView]
      rfl

/-- Call-by-call budgets for the exact sequence visited by selection. -/
def SelectionBudget (q : Query n) (b : ℕ) : ℕ → R.State → Prop
  | 0, _ => True
  | fuel + 1, s => (R.attempt s q).work ≤ b ∧
    match (R.attempt s q).value with
    | .answer _ => True
    | .refine x c => (R.refine s x c).work ≤ b ∧ SelectionBudget q b fuel (R.refine s x c).value

theorem selectLoop_work (q : Query n) (b fuel : ℕ) (s : R.State)
    (h : SelectionBudget R q b fuel s) :
    (selectLoop R q fuel s).work ≤ fuel * (2 * b + 3) + 1 := by
  induction fuel generalizing s with
  | zero => simp [selectLoop]
  | succ fuel ih =>
    have ht := h.1
    cases ha : (R.attempt s q).value with
    | answer a =>
      simp only [selectLoop, ha]
      have hn : 0 ≤ fuel * (2 * b + 3) := Nat.zero_le _
      simp only [Nat.add_mul, one_mul]
      omega
    | refine x c =>
      have hm : (R.refine s x c).work ≤ b ∧
          SelectionBudget R q b fuel (R.refine s x c).value := by
        simpa only [SelectionBudget, ha] using h.2
      have hr := ih _ hm.2
      simp only [selectLoop, ha, Nat.add_mul, one_mul]
      omega

def PathBudget (b : ℕ) : R.State → List (Fin n) → Prop
  | _, [] => True
  | s, x :: xs => (R.anchor s x).work ≤ b ∧
    (R.refine s x (R.anchor s x).value).work ≤ b ∧
      PathBudget b (R.refine s x (R.anchor s x).value).value xs

theorem pathBatch_work (b : ℕ) (s : R.State) (xs : List (Fin n))
    (h : PathBudget R b s xs) :
    (pathBatch R s xs).work ≤ xs.length * (2 * b + 3) + 1 := by
  induction xs generalizing s with
  | nil => simp [pathBatch]
  | cons x xs ih =>
    have ht := ih _ h.2.2
    have ha := h.1
    have hm := h.2.1
    simp only [pathBatch, List.length_cons, Nat.add_mul, one_mul]
    omega

def RepairBudget (b : ℕ) (s : R.State) : Prop :=
  (R.firstPath s).work ≤ b ∧
    match (R.firstPath s).value with
    | some xs => xs.length ≤ n ∧ PathBudget R b s xs
    | none => (R.degreeChoice s).work ≤ b ∧
      match (R.degreeChoice s).value with
      | none => True
      | some x => (R.anchor s x).work ≤ b ∧
        (R.refine s x (R.anchor s x).value).work ≤ b

theorem repair_work (b : ℕ) (s : R.State) (h : RepairBudget R b s) :
    (repair R s).work ≤ (n + 2) * (2 * b + 3) + 1 := by
  have hp := h.1
  cases hpath : (R.firstPath s).value with
  | some xs =>
    have hs : xs.length ≤ n ∧ PathBudget R b s xs := by
      simpa only [RepairBudget, hpath] using h.2
    have hb := pathBatch_work R b s xs hs.2
    have hm := Nat.mul_le_mul_right (2 * b + 3) hs.1
    simp only [repair, hpath]
    nlinarith
  | none =>
    have hd := h.2
    simp only [hpath] at hd
    cases hdegree : (R.degreeChoice s).value with
    | none =>
      simp only [repair, hpath, hdegree]
      have hcost := hd.1
      nlinarith
    | some x =>
      have ha : (R.anchor s x).work ≤ b ∧ (R.refine s x (R.anchor s x).value).work ≤ b := by
        simpa only [hdegree] using hd.2
      have hcost := hd.1
      simp only [repair, hpath, hdegree]
      nlinarith

def CompareBudget (b : ℕ) (s : R.State) (q : Query n) : Prop :=
  SelectionBudget R q b 3 s ∧
    match (selectLoop R q 3 s).value with
    | none => True
    | some (t, a) => (R.record t q a).work ≤ b ∧ RepairBudget R b (R.record t q a).value

theorem compare_work (b : ℕ) (s : R.State) (q : Query n) (h : CompareBudget R b s q) :
    (compare R s q).work ≤ (n + 7) * (2 * b + 3) + 5 := by
  have hsel := selectLoop_work R q b 3 s h.1
  cases hs : (selectLoop R q 3 s).value with
  | none =>
    simp only [compare, hs]
    nlinarith
  | some z =>
    obtain ⟨t, a⟩ := z
    have ha : (R.record t q a).work ≤ b ∧ RepairBudget R b (R.record t q a).value := by
      simpa only [hs] using h.2
    have hr := repair_work R b (R.record t q a).value ha.2
    simp only [compare, hs]
    nlinarith

end SortingAdversary.Continuous.ControllerWork
