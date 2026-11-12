import SortingAdversary.Continuous.EnclosureWork
import SortingAdversary.Continuous.GraphWork
import SortingAdversary.Continuous.ControllerPrecision

/-!
# Counted stored state operations

The state stores endpoint vectors, a Boolean adjacency matrix and coded
dyadic paths. Rational locations are its semantic projection, so every stored
path length is charged by the controller's depth counter. Normalization is
an actual sequence of measured conditional-bound updates, and topological
ordering uses the measured materialized closure and rank computation.
-/

namespace SortingAdversary.Continuous.StateWork

open FiniteAveraging TreeState OrderRegion EnclosureWork
open SortingAdversary.Optimal
open PrimitiveWork
open scoped BigOperators

variable {n : ℕ}

/-- Stored paths are the single source of both rational locations and anchor
codes. The projection cannot hide an unrelated, longer location list. -/
structure StoredMemory (n : ℕ) where
  data : StoredSystem n
  paths : Vector (List DyadicAnchor) n
  history : History n

def StoredMemory.memory (M : StoredMemory n) : Controller.Memory n where
  tree := ⟨M.data.system, fun x => (M.paths[x]).map DyadicAnchor.coordinate⟩
  paths x := M.paths[x]
  history := M.history

def powTwo : ℕ → PrimitiveWork.Result ℕ
  | 0 => ⟨1, 1⟩
  | e + 1 => let p := powTwo e; ⟨p.value * 2, p.work + 2⟩

@[simp] theorem powTwo_value (e : ℕ) : (powTwo e).value = 2 ^ e := by
  induction e <;> simp_all [powTwo, pow_succ]

@[simp] theorem powTwo_work (e : ℕ) : (powTwo e).work = 2 * e + 1 := by
  induction e <;> simp_all [powTwo] <;> omega

def logTwo (m : ℕ) : PrimitiveWork.Result ℕ :=
  if h : m < 2 then ⟨0, 1⟩ else
    let previous := logTwo (m / 2)
    ⟨previous.value + 1, previous.work + 3⟩
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

@[simp] theorem logTwo_value (m : ℕ) : (logTwo m).value = Nat.log 2 m := by
  unfold logTwo
  split
  · exact (Nat.log_of_lt ‹m < 2›).symm
  · dsimp only
    rw [logTwo_value (m / 2), Nat.log_div_base]
    have hp : 0 < Nat.log 2 m := Nat.log_pos (by decide) (by omega)
    omega
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem logTwo_work (m : ℕ) : (logTwo m).work = 3 * Nat.log 2 m + 1 := by
  unfold logTwo
  split
  · simp [Nat.log_of_lt ‹m < 2›]
  · dsimp only
    rw [logTwo_work (m / 2), Nat.log_div_base]
    have hp : 0 < Nat.log 2 m := Nat.log_pos (by decide) (by omega)
    omega
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def coordinate (c : DyadicAnchor) : PrimitiveWork.Result ℚ :=
  let denom := powTwo (c.1 + 1)
  ⟨(2 * c.2.val + 1 : ℚ) / denom.value, denom.work + 6⟩

@[simp] theorem coordinate_value (c : DyadicAnchor) : (coordinate c).value = c.coordinate := by
  simp [coordinate, DyadicAnchor.coordinate]

theorem coordinate_work (c : DyadicAnchor) : (coordinate c).work = 2 * (c.1 + 1) + 7 := by
  simp [coordinate]

def decode (q : ℚ) : PrimitiveWork.Result DyadicAnchor :=
  let exponent := logTwo q.den
  let m := exponent.value - 1
  let denom := powTwo m
  let anchor : DyadicAnchor := ⟨m, ⟨(q.num.toNat / 2) % denom.value, by
    change (q.num.toNat / 2) % (powTwo m).value < 2 ^ m
    rw [powTwo_value]
    exact Nat.mod_lt _ (by positivity)⟩⟩
  ⟨anchor, exponent.work + denom.work + 9⟩

@[simp] theorem decode_value (q : ℚ) : (decode q).value = DyadicAnchor.ofRat q := by
  have hm : (logTwo q.den).value - 1 = Nat.log 2 q.den - 1 :=
    congrArg (fun m => m - 1) (logTwo_value q.den)
  unfold decode DyadicAnchor.ofRat
  dsimp only
  apply Sigma.ext hm
  apply (Fin.heq_ext_iff (congrArg (fun m => 2 ^ m) hm)).mpr
  simp only [powTwo_value, logTwo_value]

theorem decode_work (q : ℚ) : (decode q).work ≤ 5 * Nat.log 2 q.den + 11 := by
  simp only [decode, logTwo_work, logTwo_value, powTwo_work]
  omega

theorem grid_log_den {q : ℚ} {F : ℕ} (hq : OnDyadicGrid F q) : Nat.log 2 q.den ≤ F := by
  have hden : q.den ≤ 2 ^ F := Nat.le_of_dvd (by positivity) (onDyadicGrid_den_dvd hq)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hden

theorem decode_work_grid (q : ℚ) (F : ℕ) (hq : OnDyadicGrid F q) :
    (decode q).work ≤ 5 * F + 11 :=
  (decode_work q).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (grid_log_den hq)) 11)

def appendOne {α : Type*} : List α → α → PrimitiveWork.Result (List α)
  | [], a => ⟨[a], 2⟩
  | x :: xs, a => let rest := appendOne xs a; ⟨x :: rest.value, rest.work + 2⟩

@[simp] theorem appendOne_value {α : Type*} (xs : List α) (a : α) :
    (appendOne xs a).value = xs ++ [a] := by
  induction xs <;> simp_all [appendOne]

theorem appendOne_work {α : Type*} (xs : List α) (a : α) :
    (appendOne xs a).work = 2 * xs.length + 2 := by
  induction xs <;> simp_all [appendOne] <;> omega

private def reverseAux {α : Type*} : List α → List α → PrimitiveWork.Result (List α)
  | [], acc => ⟨acc, 1⟩
  | x :: xs, acc => let rest := reverseAux xs (x :: acc); ⟨rest.value, rest.work + 3⟩

private theorem reverseAux_value {α : Type*} (xs acc : List α) :
    (reverseAux xs acc).value = xs.reverse ++ acc := by
  induction xs generalizing acc <;> simp_all [reverseAux, List.reverse_cons, List.append_assoc]

private theorem reverseAux_work {α : Type*} (xs acc : List α) :
    (reverseAux xs acc).work = 3 * xs.length + 1 := by
  induction xs generalizing acc <;> simp_all [reverseAux] <;> omega

def reverse {α : Type*} (xs : List α) : PrimitiveWork.Result (List α) := reverseAux xs []

@[simp] theorem reverse_value {α : Type*} (xs : List α) : (reverse xs).value = xs.reverse := by
  simp [reverse, reverseAux_value]

theorem reverse_work {α : Type*} (xs : List α) : (reverse xs).work = 3 * xs.length + 1 :=
  reverseAux_work xs []

/-- Equal prefixes compare reduced codes. Coordinates are reconstructed only
when an anchor is returned to a threshold or fixed-anchor branch. -/
def routePaths : List DyadicAnchor → List DyadicAnchor → PrimitiveWork.Result (Routing ℚ)
  | [], [] => ⟨.coordinates, 1⟩
  | [], c :: _ => let value := coordinate c; ⟨.leftFree value.value, value.work + 2⟩
  | c :: _, [] => let value := coordinate c; ⟨.rightFree value.value, value.work + 2⟩
  | c :: cs, d :: ds =>
      if c = d then let rest := routePaths cs ds; ⟨rest.value, rest.work + 4⟩ else
        let cv := coordinate c
        let dv := coordinate d
        ⟨.anchors cv.value dv.value, cv.work + dv.work + 4⟩

theorem routePaths_value (p q : List DyadicAnchor) :
    (routePaths p q).value = TreeState.route (p.map DyadicAnchor.coordinate) (q.map DyadicAnchor.coordinate) := by
  induction p generalizing q with
  | nil => cases q <;> simp [routePaths, TreeState.route]
  | cons c cs ih =>
    cases q with
    | nil => simp [routePaths, TreeState.route]
    | cons d ds =>
      by_cases h : c = d
      · subst d
        simp [routePaths, ih, TreeState.route]
      · have hc := DyadicAnchor.coordinate_injective.ne h
        simp [routePaths, TreeState.route, h, hc]

theorem routePaths_work (p q : List DyadicAnchor) (F : ℕ)
    (hp : ∀ c ∈ p, c.1 + 1 ≤ F) (hq : ∀ c ∈ q, c.1 + 1 ≤ F) :
    (routePaths p q).work ≤ (p.length + q.length + 1) * (4 * F + 20) := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp [routePaths]
    | cons c cs =>
      have hc := hq c (by simp)
      simp only [routePaths, coordinate_work, List.length_nil, List.length_cons]
      nlinarith
  | cons c cs ih =>
    cases q with
    | nil =>
      have hc := hp c (by simp)
      simp only [routePaths, coordinate_work, List.length_nil, List.length_cons]
      nlinarith
    | cons d ds =>
      have hc := hp c (by simp)
      have hd := hq d (by simp)
      have ht := ih ds (fun a ha => hp a (by simp [ha])) (fun a ha => hq a (by simp [ha]))
      simp only [routePaths, List.length_cons]
      split
      · dsimp only
        nlinarith
      · dsimp only
        rw [coordinate_work, coordinate_work]
        nlinarith

def route (M : StoredMemory n) (q : Query n) : PrimitiveWork.Result (Routing ℚ) :=
  let result := routePaths M.paths[q.left] M.paths[q.right]
  ⟨result.value, result.work + 2⟩

theorem route_value (M : StoredMemory n) (q : Query n) :
    (route M q).value = TreeState.route (M.memory.tree.location q.left) (M.memory.tree.location q.right) :=
  routePaths_value _ _

theorem path_length_le_depth (M : StoredMemory n) (x : Fin n) :
    (M.paths[x]).length ≤ Controller.totalDepth M.memory := by
  change (M.paths[x]).length ≤ ∑ y : Fin n, (M.paths[y]).length
  exact Finset.single_le_sum (f := fun y : Fin n => (M.paths[y]).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

theorem route_work (M : StoredMemory n) (q : Query n) (F : ℕ) (hF : M.memory.OnGrid F) :
    (route M q).work ≤ (2 * Controller.totalDepth M.memory + 1) * (4 * F + 20) + 2 := by
  have h := routePaths_work M.paths[q.left] M.paths[q.right] F
    (fun c hc => Controller.stored_anchor_level hF q.left c hc)
    (fun c hc => Controller.stored_anchor_level hF q.right c hc)
  have hl := path_length_le_depth M q.left
  have hr := path_length_le_depth M q.right
  have hlength : (M.paths[q.left]).length + (M.paths[q.right]).length + 1 ≤
      2 * Controller.totalDepth M.memory + 1 := by omega
  exact Nat.add_le_add_right (h.trans (Nat.mul_le_mul_right _ hlength)) 2

def reset (D : StoredSystem n) (x : Fin n) (c : ℚ) : PrimitiveWork.Result (StoredSystem n) :=
  let lower := PrimitiveWork.vector (fun y =>
    ⟨if y = x then 0 else if D.edge[x][y] then max D.lower[y] c else D.lower[y], 7⟩)
  let upper := PrimitiveWork.vector (fun y =>
    ⟨if y = x then 1 else if D.edge[y][x] then min D.upper[y] c else D.upper[y], 7⟩)
  let edge := PrimitiveWork.vector (fun y => PrimitiveWork.vector (fun z =>
    ⟨if y = x ∨ z = x then false else D.edge[y][z], 7⟩))
  ⟨⟨lower.value, upper.value, edge.value⟩, lower.work + upper.work + edge.work + 3⟩

theorem reset_value (D : StoredSystem n) (x : Fin n) (c : ℚ) :
    (reset D x c).value.system = resetCoordinate D.system x c := by
  unfold reset StoredSystem.system resetCoordinate SparseClosure.lookup
  simp only [PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]

theorem reset_work (D : StoredSystem n) (x : Fin n) (c : ℚ) :
    (reset D x c).work ≤ 30 * (n + 1) ^ 2 := by
  have hl := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = x then 0 else if D.edge[x][y] then max D.lower[y] c else D.lower[y], 7⟩ : PrimitiveWork.Result ℚ)) 7 (fun _ => le_rfl)
  have hu := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = x then 1 else if D.edge[y][x] then min D.upper[y] c else D.upper[y], 7⟩ : PrimitiveWork.Result ℚ)) 7 (fun _ => le_rfl)
  have he := PrimitiveWork.vector_work_le (fun y : Fin n => PrimitiveWork.vector (fun z : Fin n =>
    (⟨if y = x ∨ z = x then false else D.edge[y][z], 7⟩ : PrimitiveWork.Result Bool))) (n * 9)
    (fun _ => PrimitiveWork.vector_work_le _ 7 (fun _ => le_rfl))
  unfold reset
  dsimp only
  nlinarith

def propagateLower (D : StoredSystem n) (x : Fin n) : PrimitiveWork.Result (StoredSystem n) :=
  let bound := EnclosureWork.conditionalLower D x D.lower
  let lower := PrimitiveWork.vector (fun y => ⟨if y = x then bound.value else D.lower[y], 3⟩)
  ⟨{D with lower := lower.value}, bound.work + lower.work + 1⟩

def propagateUpper (D : StoredSystem n) (x : Fin n) : PrimitiveWork.Result (StoredSystem n) :=
  let bound := EnclosureWork.conditionalUpper D x D.upper
  let upper := PrimitiveWork.vector (fun y => ⟨if y = x then bound.value else D.upper[y], 3⟩)
  ⟨{D with upper := upper.value}, bound.work + upper.work + 1⟩

theorem propagateLower_value (D : StoredSystem n) (x : Fin n) :
    (propagateLower D x).value.system = OrderRegion.propagateLower D.system x := by
  simp only [propagateLower, PrimitiveWork.vector_value, StoredSystem.system,
    OrderRegion.propagateLower, Fin.getElem_fin, Vector.getElem_ofFn, EnclosureWork.conditionalLower_value]
  congr 1
  funext y
  by_cases hy : y = x <;> simp [Function.update, hy] <;> rfl

theorem propagateUpper_value (D : StoredSystem n) (x : Fin n) :
    (propagateUpper D x).value.system = OrderRegion.propagateUpper D.system x := by
  simp only [propagateUpper, PrimitiveWork.vector_value, StoredSystem.system,
    OrderRegion.propagateUpper, Fin.getElem_fin, Vector.getElem_ofFn, EnclosureWork.conditionalUpper_value]
  congr 1
  funext y
  by_cases hy : y = x <;> simp [Function.update, hy] <;> rfl

theorem propagateLower_work (D : StoredSystem n) (x : Fin n) :
    (propagateLower D x).work ≤ 16 * (n + 1) := by
  have hb := EnclosureWork.conditionalLower_work D x D.lower
  have hv := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = x then (EnclosureWork.conditionalLower D x D.lower).value else D.lower[y], 3⟩ : PrimitiveWork.Result ℚ))
    3 (fun _ => le_rfl)
  unfold propagateLower
  dsimp only
  omega

theorem propagateUpper_work (D : StoredSystem n) (x : Fin n) :
    (propagateUpper D x).work ≤ 16 * (n + 1) := by
  have hb := EnclosureWork.conditionalUpper_work D x D.upper
  have hv := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = x then (EnclosureWork.conditionalUpper D x D.upper).value else D.upper[y], 3⟩ : PrimitiveWork.Result ℚ))
    3 (fun _ => le_rfl)
  unfold propagateUpper
  dsimp only
  omega

def lowerPass : StoredSystem n → List (Fin n) → PrimitiveWork.Result (StoredSystem n)
  | D, [] => ⟨D, 1⟩
  | D, x :: xs => let next := propagateLower D x; let rest := lowerPass next.value xs
                  ⟨rest.value, next.work + rest.work + 1⟩

def upperPass : StoredSystem n → List (Fin n) → PrimitiveWork.Result (StoredSystem n)
  | D, [] => ⟨D, 1⟩
  | D, x :: xs => let next := propagateUpper D x; let rest := upperPass next.value xs
                  ⟨rest.value, next.work + rest.work + 1⟩

theorem lowerPass_value (D : StoredSystem n) (order : List (Fin n)) :
    (lowerPass D order).value.system = order.foldl OrderRegion.propagateLower D.system := by
  induction order generalizing D with
  | nil => rfl
  | cons x xs ih => simp only [lowerPass, ih, propagateLower_value, List.foldl_cons]

theorem upperPass_value (D : StoredSystem n) (order : List (Fin n)) :
    (upperPass D order).value.system = order.foldl OrderRegion.propagateUpper D.system := by
  induction order generalizing D with
  | nil => rfl
  | cons x xs ih => simp only [upperPass, ih, propagateUpper_value, List.foldl_cons]

theorem lowerPass_work (D : StoredSystem n) (order : List (Fin n)) :
    (lowerPass D order).work ≤ order.length * (16 * (n + 1) + 1) + 1 := by
  induction order generalizing D with
  | nil => simp [lowerPass]
  | cons x xs ih =>
    have hn := propagateLower_work D x
    have ht := ih (propagateLower D x).value
    simp only [lowerPass, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem upperPass_work (D : StoredSystem n) (order : List (Fin n)) :
    (upperPass D order).work ≤ order.length * (16 * (n + 1) + 1) + 1 := by
  induction order generalizing D with
  | nil => simp [upperPass]
  | cons x xs ih =>
    have hn := propagateUpper_work D x
    have ht := ih (propagateUpper D x).value
    simp only [upperPass, List.length_cons, Nat.add_mul, one_mul]
    omega

def normalize (D : StoredSystem n) (order : List (Fin n)) : PrimitiveWork.Result (StoredSystem n) :=
  let lower := lowerPass D order
  let rev := reverse order
  let upper := upperPass lower.value rev.value
  ⟨upper.value, lower.work + rev.work + upper.work + 1⟩

theorem normalize_value (D : StoredSystem n) (order : List (Fin n)) :
    (normalize D order).value.system = OrderRegion.normalize D.system order := by
  simp only [normalize, reverse_value, upperPass_value, lowerPass_value, OrderRegion.normalize]

theorem normalize_work (D : StoredSystem n) (order : List (Fin n)) :
    (normalize D order).work ≤ order.length * (32 * (n + 1) + 5) + 4 := by
  have hl := lowerPass_work D order
  have hu := upperPass_work (lowerPass D order).value order.reverse
  simp only [List.length_reverse] at hu
  simp only [normalize, reverse_value, reverse_work]
  nlinarith

private def orderedInsert {α : Type*} (compare : α → α → PrimitiveWork.Result Bool)
    (a : α) : List α → PrimitiveWork.Result (List α)
  | [] => ⟨[a], 2⟩
  | b :: bs =>
    let test := compare a b
    if test.value then ⟨a :: b :: bs, test.work + 3⟩ else
      let rest := orderedInsert compare a bs
      ⟨b :: rest.value, test.work + rest.work + 3⟩

private theorem orderedInsert_value {α : Type*} (compare : α → α → PrimitiveWork.Result Bool)
    (a : α) (xs : List α) :
    (orderedInsert compare a xs).value = List.orderedInsert (fun x y => (compare x y).value = true) a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [orderedInsert, List.orderedInsert_cons]; split <;> simp_all

private theorem orderedInsert_work {α : Type*} (compare : α → α → PrimitiveWork.Result Bool)
    (a : α) (xs : List α) (b : ℕ) (h : ∀ x y, (compare x y).work ≤ b) :
    (orderedInsert compare a xs).work ≤ xs.length * (b + 3) + 2 := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons x xs ih =>
    have hx := h a x
    simp only [orderedInsert, List.length_cons, Nat.add_mul, one_mul]
    split <;> dsimp only <;> omega

private def sort {α : Type*} (compare : α → α → PrimitiveWork.Result Bool) :
    List α → PrimitiveWork.Result (List α)
  | [] => ⟨[], 1⟩
  | a :: xs =>
    let tail := sort compare xs
    let inserted := orderedInsert compare a tail.value
    ⟨inserted.value, tail.work + inserted.work + 1⟩

private theorem sort_value {α : Type*} (compare : α → α → PrimitiveWork.Result Bool) (xs : List α) :
    (sort compare xs).value = List.insertionSort (fun x y => (compare x y).value = true) xs := by
  induction xs <;> simp_all only [sort, orderedInsert_value, List.insertionSort,
    List.foldr_nil, List.foldr_cons]

private theorem sort_work {α : Type*} (compare : α → α → PrimitiveWork.Result Bool)
    (xs : List α) (b : ℕ) (h : ∀ x y, (compare x y).work ≤ b) :
    (sort compare xs).work ≤ (xs.length + 1) ^ 2 * (b + 4) := by
  induction xs with
  | nil => simp [sort]
  | cons a xs ih =>
    have hi := orderedInsert_work compare a (sort compare xs).value b h
    rw [show (sort compare xs).value.length = xs.length by simp only [sort_value, List.length_insertionSort]] at hi
    simp only [sort, List.length_cons]
    nlinarith [Nat.zero_le (xs.length * b)]

private theorem sort_rank_value (rank : Fin n → ℕ) (hrank : Function.Injective rank) :
    (sort (fun x y => ⟨decide (rank x ≤ rank y), 3⟩) (List.finRange n)).value = rankOrder rank := by
  let r : Fin n → Fin n → Prop := fun x y => rank x ≤ rank y
  haveI : Std.Total r := ⟨fun x y => le_total (rank x) (rank y)⟩
  haveI : IsTrans (Fin n) r := ⟨fun _ _ _ => le_trans⟩
  haveI : Std.Antisymm r := ⟨fun _ _ hxy hyx => hrank (le_antisymm hxy hyx)⟩
  simp only [sort_value, decide_eq_true_eq]
  exact (List.mergeSort_eq_insertionSort r (List.finRange n)).symm

def topologicalOrder (D : StoredSystem n) : PrimitiveWork.Result (List (Fin n)) :=
  let ranks := GraphWork.closureRanks (fun x y => ⟨D.edge[x][y], 2⟩)
  let sorted := sort (fun x y => ⟨decide (ranks.value[x].val ≤ ranks.value[y].val), 3⟩) (List.finRange n)
  ⟨sorted.value, ranks.work + sorted.work + 3 * n + 1⟩

theorem topologicalOrder_value (D : StoredSystem n) :
    (topologicalOrder D).value = rankOrder (GraphOrder.graphRank D.system) := by
  let rows : ClosureWork.Rows n := fun x y => ⟨D.edge[x][y], 2⟩
  have he : ClosureWork.values rows = D.system.edge := rfl
  have hrank : Function.Injective (GraphOrder.graphRank D.system) := by
    intro x y hxy
    apply PublicOrder.extensionRank_injective (SparseClosure.closure D.system.edge)
    apply Fin.ext
    simpa only [GraphOrder.graphRank_eq] using hxy
  have heq : (fun x : Fin n => (GraphWork.closureRanks rows).value[x].val) = GraphOrder.graphRank D.system :=
    funext (GraphWork.closureRanks_graphRank D.system rows he)
  change (sort (fun x y => ⟨decide ((GraphWork.closureRanks rows).value[x].val ≤
    (GraphWork.closureRanks rows).value[y].val), 3⟩) (List.finRange n)).value = _
  have hh := sort_rank_value (fun x => (GraphWork.closureRanks rows).value[x].val)
    (by rw [heq]; exact hrank)
  simpa only [heq] using hh

def orderBound (n : ℕ) : ℕ := GraphWork.closureRanksBound n 2 + 7 * (n + 1) ^ 2 + 3 * n + 1

theorem topologicalOrder_work (D : StoredSystem n) : (topologicalOrder D).work ≤ orderBound n := by
  have hg := GraphWork.closureRanks_work (fun x y : Fin n => (⟨D.edge[x][y], 2⟩ : PrimitiveWork.Result Bool))
    2 (fun _ _ => le_rfl)
  have hs := sort_work (fun x y : Fin n =>
    (⟨decide ((GraphWork.closureRanks (fun u v => ⟨D.edge[u][v], 2⟩)).value[x].val ≤
      (GraphWork.closureRanks (fun u v => ⟨D.edge[u][v], 2⟩)).value[y].val), 3⟩ : PrimitiveWork.Result Bool))
    (List.finRange n) 3 (fun _ _ => le_rfl)
  simp only [List.length_finRange] at hs
  unfold topologicalOrder orderBound
  dsimp only
  omega

theorem topologicalOrder_length (D : StoredSystem n) : (topologicalOrder D).value.length = n := by
  rw [topologicalOrder_value, rankOrder_length]

def addArc (D : StoredSystem n) (x y : Fin n) : PrimitiveWork.Result (StoredSystem n) :=
  let edge := PrimitiveWork.vector (fun a => PrimitiveWork.vector (fun b =>
    ⟨D.edge[a][b] || decide (a = x ∧ b = y), 7⟩))
  ⟨{D with edge := edge.value}, edge.work + 1⟩

def boundBelow (D : StoredSystem n) (x : Fin n) (c : ℚ) : PrimitiveWork.Result (StoredSystem n) :=
  let upper := PrimitiveWork.vector (fun y => ⟨if y = x then min D.upper[y] c else D.upper[y], 4⟩)
  ⟨{D with upper := upper.value}, upper.work + 1⟩

def boundAbove (D : StoredSystem n) (x : Fin n) (c : ℚ) : PrimitiveWork.Result (StoredSystem n) :=
  let lower := PrimitiveWork.vector (fun y => ⟨if y = x then max D.lower[y] c else D.lower[y], 4⟩)
  ⟨{D with lower := lower.value}, lower.work + 1⟩

theorem addArc_value (D : StoredSystem n) (x y : Fin n) :
    (addArc D x y).value.system = TreeState.addArc D.system x y := by
  unfold addArc StoredSystem.system TreeState.addArc SparseClosure.lookup
  simp only [PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]

theorem boundBelow_value (D : StoredSystem n) (x : Fin n) (c : ℚ) :
    (boundBelow D x c).value.system = TreeState.boundBelow D.system x c := by
  simp only [boundBelow, StoredSystem.system, TreeState.boundBelow, PrimitiveWork.vector_value,
    Fin.getElem_fin, Vector.getElem_ofFn]
  congr 1
  funext y
  by_cases hy : y = x <;> simp [Function.update, hy]

theorem boundAbove_value (D : StoredSystem n) (x : Fin n) (c : ℚ) :
    (boundAbove D x c).value.system = TreeState.boundAbove D.system x c := by
  simp only [boundAbove, StoredSystem.system, TreeState.boundAbove, PrimitiveWork.vector_value,
    Fin.getElem_fin, Vector.getElem_ofFn]
  congr 1
  funext y
  by_cases hy : y = x <;> simp [Function.update, hy]

theorem addArc_work (D : StoredSystem n) (x y : Fin n) :
    (addArc D x y).work ≤ 12 * (n + 1) ^ 2 := by
  have he := PrimitiveWork.vector_work_le (fun a : Fin n => PrimitiveWork.vector (fun b : Fin n =>
    (⟨D.edge[a][b] || decide (a = x ∧ b = y), 7⟩ : PrimitiveWork.Result Bool))) (n * 9)
    (fun _ => PrimitiveWork.vector_work_le _ 7 (fun _ => le_rfl))
  unfold addArc
  dsimp only
  nlinarith

theorem boundBelow_work (D : StoredSystem n) (x : Fin n) (c : ℚ) :
    (boundBelow D x c).work ≤ 6 * n + 1 := by
  have hv := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = x then min D.upper[y] c else D.upper[y], 4⟩ : PrimitiveWork.Result ℚ)) 4 (fun _ => le_rfl)
  unfold boundBelow
  dsimp only
  omega

theorem boundAbove_work (D : StoredSystem n) (x : Fin n) (c : ℚ) :
    (boundAbove D x c).work ≤ 6 * n + 1 := by
  have hv := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = x then max D.lower[y] c else D.lower[y], 4⟩ : PrimitiveWork.Result ℚ)) 4 (fun _ => le_rfl)
  unfold boundAbove
  dsimp only
  omega

def recordSystem (D : StoredSystem n) (r : Routing ℚ) (x y : Fin n) (a : Answer) :
    PrimitiveWork.Result (StoredSystem n) :=
  let next := match r, a with
    | .coordinates, .less => addArc D x y
    | .coordinates, .greater => addArc D y x
    | .leftFree c, .less => boundBelow D x c
    | .leftFree c, .greater => boundAbove D x c
    | .rightFree c, .less => boundAbove D y c
    | .rightFree c, .greater => boundBelow D y c
    | .anchors _ _, _ => ⟨D, 1⟩
  ⟨next.value, next.work + 2⟩

theorem recordSystem_value (D : StoredSystem n) (r : Routing ℚ) (x y : Fin n) (a : Answer) :
    (recordSystem D r x y a).value.system = TreeState.recordSystem D.system r x y a := by
  cases r <;> cases a <;>
    simp only [recordSystem, TreeState.recordSystem, addArc_value, boundBelow_value, boundAbove_value]

theorem recordSystem_work (D : StoredSystem n) (r : Routing ℚ) (x y : Fin n) (a : Answer) :
    (recordSystem D r x y a).work ≤ 15 * (n + 1) ^ 2 := by
  have hn : 1 ≤ (n + 1) ^ 2 := by
    have hp : 0 < (n + 1) ^ 2 := pow_pos (by omega) 2
    omega
  cases r with
  | coordinates =>
    have hxy := addArc_work D x y
    have hyx := addArc_work D y x
    cases a <;> simp only [recordSystem] <;> nlinarith
  | leftFree c =>
    have hl := boundBelow_work D x c
    have hu := boundAbove_work D x c
    cases a <;> simp only [recordSystem] <;> nlinarith
  | rightFree c =>
    have hl := boundBelow_work D y c
    have hu := boundAbove_work D y c
    cases a <;> simp only [recordSystem] <;> nlinarith
  | anchors c d => cases a <;> simp [recordSystem] <;> nlinarith

def makeMove (M : StoredMemory n) (x : Fin n) (q : ℚ) : PrimitiveWork.Result (TraceAccounting.Move n) :=
  let anchor := decode q
  let value := coordinate anchor.value
  let next := reset M.data x value.value
  let order := topologicalOrder next.value
  ⟨⟨x, anchor.value, order.value⟩, anchor.work + value.work + next.work + order.work + 1⟩

theorem makeMove_value (M : StoredMemory n) (x : Fin n) (q : ℚ) :
    (makeMove M x q).value = Controller.makeMove M.memory x q := by
  simp only [makeMove, decode_value, coordinate_value, topologicalOrder_value, reset_value,
    Controller.makeMove, StoredMemory.memory]

def applyMove (M : StoredMemory n) (m : TraceAccounting.Move n) : PrimitiveWork.Result (StoredMemory n) :=
  let value := coordinate m.anchor
  let next := reset M.data m.item value.value
  let normalized := normalize next.value m.order
  let path := appendOne M.paths[m.item] m.anchor
  let paths := PrimitiveWork.vector (fun y => ⟨if y = m.item then path.value else M.paths[y], 3⟩)
  ⟨⟨normalized.value, paths.value, M.history⟩,
    value.work + next.work + normalized.work + path.work + paths.work + 3⟩

private theorem memory_ext {M N : Controller.Memory n}
    (hs : M.tree.system = N.tree.system) (hl : M.tree.location = N.tree.location)
    (hp : M.paths = N.paths) (hh : M.history = N.history) : M = N := by
  rcases M with ⟨⟨ms, ml⟩, mp, mh⟩
  rcases N with ⟨⟨ns, nl⟩, np, nh⟩
  dsimp only at hs hl hp hh
  subst ns
  subst nl
  subst np
  subst nh
  rfl

theorem applyMove_value (M : StoredMemory n) (m : TraceAccounting.Move n) :
    (applyMove M m).value.memory = Controller.applyMove M.memory m := by
  apply memory_ext
  · simp only [applyMove, StoredMemory.memory, Controller.applyMove, TreeState.normalize,
      refineAt, normalize_value, reset_value, coordinate_value]
  · funext y
    simp only [applyMove, StoredMemory.memory, Controller.applyMove, TreeState.normalize,
      refineAt, PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn, appendOne_value]
    by_cases hy : y = m.item <;> simp [Function.update, hy, List.map_append]
  · funext y
    simp only [applyMove, StoredMemory.memory, Controller.applyMove,
      PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn, appendOne_value]
    by_cases hy : y = m.item <;> simp [Function.update, hy]
  · rfl

def refine (M : StoredMemory n) (x : Fin n) (c : ℚ) : PrimitiveWork.Result (StoredMemory n) :=
  let move := makeMove M x c
  let next := applyMove M move.value
  ⟨next.value, move.work + next.work + 1⟩

theorem refine_value (M : StoredMemory n) (x : Fin n) (c : ℚ) :
    (refine M x c).value.memory = Controller.applyMove M.memory (Controller.makeMove M.memory x c) := by
  simp only [refine, applyMove_value, makeMove_value]

def record (M : StoredMemory n) (q : Query n) (a : Answer) : PrimitiveWork.Result (StoredMemory n) :=
  let routing := route M q
  let next := recordSystem M.data routing.value q.left q.right a
  let order := topologicalOrder next.value
  let normalized := normalize next.value order.value
  ⟨⟨normalized.value, M.paths, ⟨q, a⟩ :: M.history⟩,
    routing.work + next.work + order.work + normalized.work + 4⟩

theorem record_value (M : StoredMemory n) (q : Query n) (a : Answer) :
    (record M q a).value.memory = Controller.recorded M.memory q a := by
  apply memory_ext
  · simp only [record, StoredMemory.memory, normalize_value, topologicalOrder_value, recordSystem_value,
      route_value, Controller.recorded, Controller.applyAction, TreeState.normalize,
      TreeState.record, Controller.answerOrder]
  · rfl
  · rfl
  · rfl

theorem decode_level_grid (q : ℚ) (F : ℕ) (hq : OnDyadicGrid F q) :
    (decode q).value.1 + 1 ≤ F + 1 := by
  rw [decode_value]
  change Nat.log 2 q.den - 1 + 1 ≤ F + 1
  have h := grid_log_den hq
  omega

theorem makeMove_work (M : StoredMemory n) (x : Fin n) (q : ℚ) (F : ℕ)
    (hq : OnDyadicGrid F q) :
    (makeMove M x q).work ≤ orderBound n + 30 * (n + 1) ^ 2 + 7 * F + 22 := by
  have ha := decode_work_grid q F hq
  have hl := decode_level_grid q F hq
  have hc := coordinate_work (decode q).value
  have hd := reset_work M.data x (coordinate (decode q).value).value
  have ho := topologicalOrder_work (reset M.data x (coordinate (decode q).value).value).value
  unfold makeMove
  dsimp only
  omega

def applyMoveBound (n depth orderLength level : ℕ) : ℕ :=
  30 * (n + 1) ^ 2 + orderLength * (32 * (n + 1) + 5) +
    2 * (level + 1) + 2 * depth + 5 * n + 20

theorem applyMove_work (M : StoredMemory n) (m : TraceAccounting.Move n) :
    (applyMove M m).work ≤ applyMoveBound n (Controller.totalDepth M.memory) m.order.length m.anchor.1 := by
  have hc := coordinate_work m.anchor
  have hd := reset_work M.data m.item (coordinate m.anchor).value
  have hn := normalize_work (reset M.data m.item (coordinate m.anchor).value).value m.order
  have hp := appendOne_work M.paths[m.item] m.anchor
  have hv := PrimitiveWork.vector_work_le (fun y : Fin n =>
    (⟨if y = m.item then (appendOne M.paths[m.item] m.anchor).value else M.paths[y], 3⟩ :
      PrimitiveWork.Result (List DyadicAnchor))) 3 (fun _ => le_rfl)
  have hdepth := path_length_le_depth M m.item
  unfold applyMove applyMoveBound
  dsimp only
  omega

def refineBound (n depth F : ℕ) : ℕ :=
  orderBound n + 100 * (n + 1) ^ 2 + 10 * F + 2 * depth + 60

theorem refine_work (M : StoredMemory n) (x : Fin n) (q : ℚ) (F : ℕ)
    (hq : OnDyadicGrid F q) :
    (refine M x q).work ≤ refineBound n (Controller.totalDepth M.memory) F := by
  have hm := makeMove_work M x q F hq
  have ha := applyMove_work M (makeMove M x q).value
  have hl : (makeMove M x q).value.order.length = n := by
    simp only [makeMove_value, Controller.makeMove, rankOrder_length]
  have hc : (makeMove M x q).value.anchor.1 + 1 ≤ F + 1 := decode_level_grid q F hq
  rw [hl] at ha
  unfold applyMoveBound at ha
  unfold refine refineBound
  dsimp only
  nlinarith

def recordBound (n depth F : ℕ) : ℕ :=
  orderBound n + 60 * (n + 1) ^ 2 + (2 * depth + 1) * (4 * F + 20) + 10

theorem record_work (M : StoredMemory n) (q : Query n) (a : Answer) (F : ℕ)
    (hF : M.memory.OnGrid F) :
    (record M q a).work ≤ recordBound n (Controller.totalDepth M.memory) F := by
  have hr := route_work M q F hF
  have hd := recordSystem_work M.data (route M q).value q.left q.right a
  have ho := topologicalOrder_work (recordSystem M.data (route M q).value q.left q.right a).value
  have hn := normalize_work (recordSystem M.data (route M q).value q.left q.right a).value
    (topologicalOrder (recordSystem M.data (route M q).value q.left q.right a).value).value
  rw [topologicalOrder_length] at hn
  unfold record recordBound
  dsimp only
  nlinarith

def initial (n : ℕ) : PrimitiveWork.Result (StoredMemory n) :=
  let lower := PrimitiveWork.vector (fun _ : Fin n => (⟨0, 1⟩ : PrimitiveWork.Result ℚ))
  let upper := PrimitiveWork.vector (fun _ : Fin n => (⟨1, 1⟩ : PrimitiveWork.Result ℚ))
  let edge := PrimitiveWork.vector (fun _ : Fin n => PrimitiveWork.vector (fun _ : Fin n => ⟨false, 1⟩))
  let paths := PrimitiveWork.vector (fun _ : Fin n => (⟨[], 1⟩ : PrimitiveWork.Result (List DyadicAnchor)))
  ⟨⟨⟨lower.value, upper.value, edge.value⟩, paths.value, []⟩,
    lower.work + upper.work + edge.work + paths.work + 4⟩

theorem initial_value (n : ℕ) : (initial n).value.memory = Controller.initial n := by
  apply memory_ext
  · unfold initial StoredMemory.memory StoredSystem.system Controller.initial TreeState.initial SparseClosure.lookup
    simp only [PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]
  · funext x
    simp only [initial, StoredMemory.memory, Controller.initial, TreeState.initial,
      PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn, List.map_nil]
  · funext x
    simp only [initial, StoredMemory.memory, Controller.initial,
      PrimitiveWork.vector_value, Fin.getElem_fin, Vector.getElem_ofFn]
  · rfl

theorem initial_work (n : ℕ) : (initial n).work ≤ 12 * (n + 1) ^ 2 := by
  have hl := PrimitiveWork.vector_work_le (fun _ : Fin n => (⟨0, 1⟩ : PrimitiveWork.Result ℚ)) 1 (fun _ => le_rfl)
  have hu := PrimitiveWork.vector_work_le (fun _ : Fin n => (⟨1, 1⟩ : PrimitiveWork.Result ℚ)) 1 (fun _ => le_rfl)
  have hp := PrimitiveWork.vector_work_le (fun _ : Fin n => (⟨[], 1⟩ : PrimitiveWork.Result (List DyadicAnchor))) 1 (fun _ => le_rfl)
  have he := PrimitiveWork.vector_work_le (fun _ : Fin n => PrimitiveWork.vector (fun _ : Fin n =>
    (⟨false, 1⟩ : PrimitiveWork.Result Bool))) (n * 3)
    (fun _ => PrimitiveWork.vector_work_le _ 1 (fun _ => le_rfl))
  unfold initial
  dsimp only
  nlinarith

/-- Every integer reconstructed from a stored anchor fits the same grid
scale as its rational coordinate; the bound includes the power loop. -/
theorem anchor_operands (M : StoredMemory n) (F : ℕ) (hF : M.memory.OnGrid F)
    (x : Fin n) (c : DyadicAnchor) (hc : c ∈ M.paths[x]) :
    c.1 + 1 ≤ F ∧ c.2.val < 2 ^ F ∧ 2 * c.2.val + 1 < 2 ^ F ∧
      (powTwo (c.1 + 1)).value ≤ 2 ^ F ∧
      c.coordinate.den.size ≤ F + 1 ∧ c.coordinate.num.natAbs.size ≤ F + 1 := by
  have hl := Controller.stored_anchor_level hF x c hc
  have hi := c.2.isLt
  have hp : 2 ^ (c.1 + 1) ≤ 2 ^ F := Nat.pow_le_pow_right (by decide) hl
  have hnum : 2 * c.2.val + 1 < 2 ^ (c.1 + 1) := by
    rw [pow_succ]
    omega
  have hbits := Controller.stored_anchor_bits hF x c hc
  refine ⟨hl, ?_, hnum.trans_le hp, ?_, hbits⟩
  · exact hi.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · simpa only [powTwo_value] using hp

end SortingAdversary.Continuous.StateWork
