import SortingAdversary.Optimal.ScaleWalks
import SortingAdversary.Optimal.PrimitiveWork

/-!
# Counted breadth matrices and exact deterministic shortest walks

The counted implementation stores each breadth layer as a Boolean matrix.
This realizes finite-set union by a bounded scan, including list generation,
indexed reads and every input-row callback. The value is the same breadth
relation as `ScaleWalks.reachTable`; later reconstruction retains its exact
least-label tie break. No input predicate is assumed to have unit cost.
-/

namespace SortingAdversary.Optimal.ScaleWalksWork

open scoped BigOperators
open GraphBalls ScaleGeometry PrimitiveWork

variable {n : ℕ}

abbrev Rows (n : ℕ) := Fin n → Fin n → Result Bool
abbrev Matrix (n : ℕ) := Vector (Vector Bool n) n

def relation (E : Rows n) (x y : Fin n) : Bool := (E x y).value

def anyFin (f : Fin n → Result Bool) : Result Bool :=
  let found := PrimitiveWork.any f (List.finRange n)
  ⟨found.value, found.work + 2 * n + 1⟩

def findFin (f : Fin n → Result Bool) : Result (Option (Fin n)) :=
  let found := PrimitiveWork.find f (List.finRange n)
  ⟨found.value, found.work + 2 * n + 1⟩

@[simp] theorem anyFin_value (f : Fin n → Result Bool) :
    (anyFin f).value = (List.finRange n).any (fun i => (f i).value) := by
  simp [anyFin]

@[simp] theorem findFin_value (f : Fin n → Result Bool) :
    (findFin f).value = (List.finRange n).find? (fun i => (f i).value) := by
  simp [findFin]

theorem anyFin_work (f : Fin n → Result Bool) (bound : ℕ) (h : ∀ i, (f i).work ≤ bound) :
    (anyFin f).work ≤ n * (bound + 4) + 3 := by
  have hh := any_work_le f (List.finRange n) bound (fun i _ => h i)
  simp only [List.length_finRange] at hh
  change (PrimitiveWork.any f _).work + 2 * n + 1 ≤ _
  simp only [Nat.mul_add] at hh ⊢
  omega

theorem findFin_work (f : Fin n → Result Bool) (bound : ℕ) (h : ∀ i, (f i).work ≤ bound) :
    (findFin f).work ≤ n * (bound + 4) + 2 := by
  have hh := find_work_le f (List.finRange n) bound (fun i _ => h i)
  simp only [List.length_finRange] at hh
  change (PrimitiveWork.find f _).work + 2 * n + 1 ≤ _
  simp only [Nat.mul_add] at hh ⊢
  omega

def neighbor (E : Rows n) (x y : Fin n) : Result Bool :=
  let forward := E x y
  let backward := E y x
  ⟨decide (y = x) || forward.value || backward.value, forward.work + backward.work + 3⟩

@[simp] theorem neighbor_true (E : Rows n) (x y : Fin n) :
    (neighbor E x y).value = true ↔ y ∈ closedNeighbors (relation E) x := by
  simp [neighbor, relation, Bool.or_eq_true, or_assoc]

theorem neighbor_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C) (x y : Fin n) :
    (neighbor E x y).work ≤ 2 * C + 3 := by
  have hf := cost x y
  have hb := cost y x
  change (E x y).work + (E y x).work + 3 ≤ _
  omega

def stepTest (E : Rows n) (old : Matrix n) (x y u : Fin n) : Result Bool :=
  let adjacent := neighbor E x u
  ⟨adjacent.value && old[u][y], adjacent.work + 3⟩

def layer (E : Rows n) (old : Matrix n) : Result (Matrix n) :=
  vector (fun x => vector (fun y => anyFin (stepTest E old x y)))

def reach (E : Rows n) : ℕ → Result (Matrix n)
  | 0 =>
    let base := vector (fun x => vector (fun y => atom (decide (y = x))))
    ⟨base.value, base.work + 1⟩
  | r + 1 =>
    let old := reach E r
    let next := layer E old.value
    ⟨next.value, old.work + next.work + 2⟩

theorem reach_true (E : Rows n) (r : ℕ) (x y : Fin n) :
    (reach E r).value[x][y] = true ↔ y ∈ ball (relation E) x r := by
  induction r generalizing x y with
  | zero => simp [reach, atom, ball]
  | succ r ih =>
    simp only [Fin.getElem_fin] at ih
    simp only [reach, layer, vector_value, Fin.getElem_fin, Vector.getElem_ofFn, anyFin_value, List.any_eq_true,
      List.mem_finRange, true_and, stepTest, Bool.and_eq_true, neighbor_true, ih, mem_ball_succ]

/-- Exact equality with the existing finite-set breadth table, coordinate
by coordinate, without evaluating a semantic union tree. -/
theorem reachTable_value (E : Rows n) (r : ℕ) (x y : Fin n) :
    (reach E r).value[x][y] = decide (y ∈ (ScaleWalks.reachTable (relation E) r)[x]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [reach_true, decide_eq_true_eq, ScaleWalks.reachTable_get]

def baseBound (n : ℕ) : ℕ := n * (3 * n + 2) + 1
def layerBound (n C : ℕ) : ℕ := n * (n * (n * (2 * C + 10) + 5) + 2) + 2
def reachBound (n r C : ℕ) : ℕ := baseBound n + r * layerBound n C

theorem layer_work (E : Rows n) (old : Matrix n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C) :
    (layer E old).work + 2 ≤ layerBound n C := by
  have ht (x y u : Fin n) : (stepTest E old x y u).work ≤ 2 * C + 6 := by
    have hh := neighbor_work E C cost x u
    change (neighbor E x u).work + 3 ≤ _
    omega
  have ha (x y : Fin n) : (anyFin (stepTest E old x y)).work ≤ n * (2 * C + 10) + 3 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using anyFin_work (stepTest E old x y) (2 * C + 6) (ht x y)
  have hi (x : Fin n) :
      (vector (fun y => anyFin (stepTest E old x y))).work ≤ n * (n * (2 * C + 10) + 5) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using vector_work_le _ (n * (2 * C + 10) + 3) (ha x)
  have ho := vector_work_le (fun x => vector (fun y => anyFin (stepTest E old x y)))
    (n * (n * (2 * C + 10) + 5)) hi
  exact Nat.add_le_add_right ho 2

theorem reach_work (E : Rows n) (r C : ℕ) (cost : ∀ x y, (E x y).work ≤ C) :
    (reach E r).work ≤ reachBound n r C := by
  induction r with
  | zero =>
    have hi (x : Fin n) : (vector (fun y : Fin n => atom (decide (y = x)))).work ≤ 3 * n := by
      simpa [atom, Nat.mul_comm] using vector_work_le (fun y : Fin n => atom (decide (y = x))) 1 (fun _ => le_rfl)
    have ho := vector_work_le (fun x : Fin n => vector (fun y => atom (decide (y = x)))) (3 * n) hi
    simpa only [reach, reachBound, baseBound, Nat.zero_mul, Nat.add_zero] using Nat.add_le_add_right ho 1
  | succ r ih =>
    have hn := layer_work E (reach E r).value C cost
    change (reach E r).work + (layer E (reach E r).value).work + 2 ≤ _
    unfold reachBound at ih ⊢
    rw [Nat.add_mul, one_mul]
    omega

theorem reachBound_mono (n C : ℕ) {r s : ℕ} (h : r ≤ s) : reachBound n r C ≤ reachBound n s C :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem find_min (predicate : Fin n → Bool)
    (nonempty : (Finset.univ.filter (fun x => predicate x = true)).Nonempty) :
    (List.finRange n).find? predicate = some ((Finset.univ.filter (fun x => predicate x = true)).min' nonempty) := by
  rw [← List.ofFn_id, List.find?_ofFn_eq_some]
  let chosen := (Finset.univ.filter (fun x => predicate x = true)).min' nonempty
  have hm : chosen ∈ Finset.univ.filter (fun x => predicate x = true) := Finset.min'_mem _ _
  refine ⟨(Finset.mem_filter.mp hm).2, chosen, rfl, ?_⟩
  intro j hj test
  have hmin := Finset.min'_le (Finset.univ.filter (fun x => predicate x = true)) j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, test⟩)
  exact (not_lt_of_ge hmin) hj

/-- A bounded search over radii; each tested breadth table is paid for. -/
def distanceSearch (E : Rows n) (x y : Fin n) : Result (Option (Fin (n + 1))) :=
  findFin (fun r =>
    let table := reach E r.val
    ⟨table.value[x][y], table.work + 2⟩)

theorem distanceSearch_value (E : Rows n) (x y : Fin n)
    (hc : Connected (relation E) x y) :
    (distanceSearch E x y).value = some (ScaleWalks.distance (relation E) x y hc) := by
  have hset : Finset.univ.filter (fun r : Fin (n + 1) => (reach E r.val).value[x][y] = true) =
      ScaleWalks.distanceCandidates (relation E) x y := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, reach_true,
      ScaleWalks.mem_distanceCandidates]
  have hn := ScaleWalks.distanceCandidates_nonempty (relation E) x y hc
  have hn' : (Finset.univ.filter (fun r : Fin (n + 1) => (reach E r.val).value[x][y] = true)).Nonempty := by
    rw [hset]
    exact hn
  change (findFin (fun r : Fin (n + 1) =>
    ⟨(reach E r.val).value[x][y], (reach E r.val).work + 2⟩)).value = _
  rw [findFin_value, find_min _ hn']
  simp only [hset, ScaleWalks.distance]

def distance (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y) : Result (Fin (n + 1)) :=
  let found := distanceSearch E x y
  have hs : found.value.isSome = true := by rw [distanceSearch_value E x y hc]; rfl
  ⟨found.value.get hs, found.work + 1⟩

@[simp] theorem distance_value (E : Rows n) (x y : Fin n)
    (hc : Connected (relation E) x y) :
    (distance E x y hc).value = ScaleWalks.distance (relation E) x y hc := by
  simp only [distance, distanceSearch_value E x y hc, Option.get_some]

def distanceBound (n C : ℕ) : ℕ := (n + 1) * (reachBound n n C + 6) + 3

theorem distance_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C)
    (x y : Fin n) (hc : Connected (relation E) x y) :
    (distance E x y hc).work ≤ distanceBound n C := by
  have hr (r : Fin (n + 1)) : (reach E r.val).work + 2 ≤ reachBound n n C + 2 :=
    Nat.add_le_add_right ((reach_work E r.val C cost).trans
      (reachBound_mono n C (Nat.le_of_lt_succ r.isLt))) 2
  have hh := findFin_work (fun r : Fin (n + 1) =>
    (⟨(reach E r.val).value[x][y], (reach E r.val).work + 2⟩ : Result Bool))
    (reachBound n n C + 2) hr
  simp only [Nat.add_assoc, Nat.reduceAdd] at hh
  exact Nat.add_le_add_right hh 1

/-- Cache the breadth matrix before scanning the next-label candidates. -/
def nextSearch (E : Rows n) (x y : Fin n) (r : ℕ) : Result (Option (Fin n)) :=
  let table := reach E r
  let found := findFin (stepTest E table.value x y)
  ⟨found.value, table.work + found.work⟩

theorem nextSearch_value (E : Rows n) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball (relation E) x (r + 1)) :
    (nextSearch E x y r).value = some (ScaleWalks.nextLabel (relation E) x y r h) := by
  have hset : Finset.univ.filter
      (fun u => (stepTest E (reach E r).value x y u).value = true) =
      ScaleWalks.candidates (relation E) x y r := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, stepTest, Bool.and_eq_true,
      neighbor_true, reach_true, ScaleWalks.mem_candidates]
  have hn' : (Finset.univ.filter
      (fun u => (stepTest E (reach E r).value x y u).value = true)).Nonempty := by
    rw [hset]
    exact ScaleWalks.candidates_nonempty (relation E) x y r h
  change (findFin (stepTest E (reach E r).value x y)).value = _
  rw [findFin_value, find_min _ hn']
  simp only [hset, ScaleWalks.nextLabel]

def nextLabel (E : Rows n) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball (relation E) x (r + 1)) : Result (Fin n) :=
  let found := nextSearch E x y r
  have hs : found.value.isSome = true := by rw [nextSearch_value E x y r h]; rfl
  ⟨found.value.get hs, found.work + 1⟩

@[simp] theorem nextLabel_value (E : Rows n) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball (relation E) x (r + 1)) :
    (nextLabel E x y r h).value = ScaleWalks.nextLabel (relation E) x y r h := by
  simp only [nextLabel, nextSearch_value E x y r h, Option.get_some]

def nextBound (n r C : ℕ) : ℕ := reachBound n r C + n * (2 * C + 10) + 3

theorem nextLabel_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C)
    (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x (r + 1)) :
    (nextLabel E x y r h).work ≤ nextBound n r C := by
  have ht (u : Fin n) : (stepTest E (reach E r).value x y u).work ≤ 2 * C + 6 := by
    have hh := neighbor_work E C cost x u
    change (neighbor E x u).work + 3 ≤ _
    omega
  have hf := findFin_work (stepTest E (reach E r).value x y) (2 * C + 6) ht
  simp only [Nat.add_assoc, Nat.reduceAdd] at hf
  have hr := reach_work E r C cost
  change (reach E r).work + (findFin (stepTest E (reach E r).value x y)).work + 1 ≤ _
  unfold nextBound
  omega

/-- Reconstruct the same walk as the original deterministic routine. Proof
fields erase; each actual recursive call and constructor is counted. -/
def buildWalk (E : Rows n) (x y : Fin n) : (r : ℕ) → y ∈ ball (relation E) x r →
    Result {p : Walk (relation E) r // p.start = x ∧ p.finish = y}
  | 0, h => ⟨⟨Walk.single (relation E) x, rfl, by
      have hy : y = x := by simpa only [ball_zero, Finset.mem_singleton] using h
      exact hy.symm⟩, 3⟩
  | r + 1, h =>
    let u := nextLabel E x y r h
    have hu : u.value ∈ closedNeighbors (relation E) x ∧ y ∈ ball (relation E) u.value r := by
      change (nextLabel E x y r h).value ∈ closedNeighbors (relation E) x ∧
        y ∈ ball (relation E) (nextLabel E x y r h).value r
      rw [nextLabel_value]
      exact ScaleWalks.nextLabel_spec (relation E) x y r h
    let tail := buildWalk E u.value y r hu.2
    ⟨⟨tail.value.val.prepend x (by rw [tail.value.property.1]; exact hu.1), rfl,
      tail.value.property.2⟩, u.work + tail.work + 3⟩

private theorem prepend_congr (E : Rows n) (x y : Fin n) (r : ℕ) {u v : Fin n}
    (heq : u = v)
    (hu : u ∈ closedNeighbors (relation E) x ∧ y ∈ ball (relation E) u r)
    (hv : v ∈ closedNeighbors (relation E) x ∧ y ∈ ball (relation E) v r) :
    ((ScaleWalks.buildWalk (relation E) u y r hu.2).val.prepend x
      (by rw [(ScaleWalks.buildWalk (relation E) u y r hu.2).property.1]; exact hu.1)) =
    ((ScaleWalks.buildWalk (relation E) v y r hv.2).val.prepend x
      (by rw [(ScaleWalks.buildWalk (relation E) v y r hv.2).property.1]; exact hv.1)) := by
  subst v
  rfl

@[simp] theorem buildWalk_value (E : Rows n) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball (relation E) x r) :
    (buildWalk E x y r h).value = ScaleWalks.buildWalk (relation E) x y r h := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih =>
    simp only [buildWalk, ScaleWalks.buildWalk, ih]
    apply Subtype.ext
    exact prepend_congr E x y r (nextLabel_value E x y r h)
      (by rw [nextLabel_value]; exact ScaleWalks.nextLabel_spec (relation E) x y r h)
      (ScaleWalks.nextLabel_spec (relation E) x y r h)

def walkBound (n r C : ℕ) : ℕ := 3 + r * (reachBound n r C + n * (2 * C + 10) + 6)

theorem buildWalk_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C)
    (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x r) :
    (buildWalk E x y r h).work ≤ walkBound n r C := by
  induction r generalizing x y with
  | zero => simp [buildWalk, walkBound]
  | succ r ih =>
    have hu := nextLabel_work E C cost x y r h
    have ht := ih (nextLabel E x y r h).value y
      (by simpa only [nextLabel_value] using (ScaleWalks.nextLabel_spec (relation E) x y r h).2)
    have hm := reachBound_mono n C (Nat.le_succ r)
    change (nextLabel E x y r h).work + (buildWalk E _ y r _).work + 3 ≤ _
    unfold walkBound at ht ⊢
    unfold nextBound at hu
    have hp := Nat.mul_le_mul_left r (Nat.add_le_add_right (Nat.add_le_add_right hm (n * (2 * C + 10))) 6)
    simp only [Nat.succ_eq_add_one] at hm hp
    rw [Nat.add_mul, one_mul]
    omega

theorem walkBound_mono (n C : ℕ) {r s : ℕ} (h : r ≤ s) : walkBound n r C ≤ walkBound n s C := by
  unfold walkBound
  exact Nat.add_le_add_left (Nat.mul_le_mul h
    (Nat.add_le_add_right (Nat.add_le_add_right (reachBound_mono n C h) _) _)) 3

/-- A counted shortest-walk computation, with exact original label ties. -/
def shortestPath (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y) :
    Result (ScaleWalks.ShortestPath (relation E) x y) :=
  let radius := distance E x y hc
  have reaches : y ∈ ball (relation E) x radius.value.val := by
    rw [distance_value]
    exact ScaleWalks.distance_reaches (relation E) x y hc
  let path := buildWalk E x y radius.value.val reaches
  ⟨{ length := radius.value.val
     walk := path.value.val
     start := path.value.property.1
     finish := path.value.property.2
     shortest := by
       change ∀ r, y ∈ ball (relation E) x r → (distance E x y hc).value.val ≤ r
       simpa only [distance_value] using ScaleWalks.distance_minimal (relation E) x y hc
     length_bound := Nat.le_of_lt_succ radius.value.isLt },
    radius.work + path.work + 4⟩

private theorem shortest_congr (E : Rows n) (x y : Fin n) {r s : Fin (n + 1)} (heq : r = s)
    (hr : y ∈ ball (relation E) x r.val) (hs : y ∈ ball (relation E) x s.val)
    (mr : ∀ t, y ∈ ball (relation E) x t → r.val ≤ t)
    (ms : ∀ t, y ∈ ball (relation E) x t → s.val ≤ t) :
    ({ length := r.val, walk := (ScaleWalks.buildWalk (relation E) x y r.val hr).val,
       start := (ScaleWalks.buildWalk (relation E) x y r.val hr).property.1,
       finish := (ScaleWalks.buildWalk (relation E) x y r.val hr).property.2,
       shortest := mr, length_bound := Nat.le_of_lt_succ r.isLt } : ScaleWalks.ShortestPath (relation E) x y) =
    { length := s.val, walk := (ScaleWalks.buildWalk (relation E) x y s.val hs).val,
       start := (ScaleWalks.buildWalk (relation E) x y s.val hs).property.1,
       finish := (ScaleWalks.buildWalk (relation E) x y s.val hs).property.2,
       shortest := ms, length_bound := Nat.le_of_lt_succ s.isLt } := by
  subst s
  rfl

@[simp] theorem shortestPath_value (E : Rows n) (x y : Fin n) (hc : Connected (relation E) x y) :
    (shortestPath E x y hc).value = ScaleWalks.shortestPath (relation E) x y hc := by
  simp only [shortestPath, ScaleWalks.shortestPath, buildWalk_value]
  exact shortest_congr E x y (distance_value E x y hc) _ _ _ _

def shortestBound (n C : ℕ) : ℕ := distanceBound n C + walkBound n n C + 4

theorem shortestPath_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C)
    (x y : Fin n) (hc : Connected (relation E) x y) :
    (shortestPath E x y hc).work ≤ shortestBound n C := by
  have hd := distance_work E C cost x y hc
  have hp := buildWalk_work E C cost x y (distance E x y hc).value.val
    (by rw [distance_value]; exact ScaleWalks.distance_reaches (relation E) x y hc)
  have hm := walkBound_mono n C (Nat.le_of_lt_succ (distance E x y hc).value.isLt)
  change (distance E x y hc).work + (buildWalk E x y _ _).work + 4 ≤ _
  unfold shortestBound
  omega

def shortestPath? (E : Rows n) (x y : Fin n) : Result (Option (ScaleWalks.ShortestPath (relation E) x y)) :=
  let table := reach E n
  if h : table.value[x][y] = true then
    let path := shortestPath E x y ⟨n, (reach_true E n x y).mp h⟩
    ⟨some path.value, table.work + path.work + 4⟩
  else ⟨none, table.work + 3⟩

@[simp] theorem shortestPath?_value (E : Rows n) (x y : Fin n) :
    (shortestPath? E x y).value = ScaleWalks.shortestPath? (relation E) x y := by
  simp only [shortestPath?, ScaleWalks.shortestPath?, ScaleWalks.connected, ← reachTable_value]
  split_ifs with h
  · exact congrArg some (shortestPath_value E x y ⟨n, (reach_true E n x y).mp h⟩)
  · rfl

theorem shortestPath?_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C)
    (x y : Fin n) :
    (shortestPath? E x y).work ≤ reachBound n n C + shortestBound n C + 4 := by
  have hr := reach_work E n C cost
  unfold shortestPath?
  dsimp only
  split_ifs with h
  · have hp := shortestPath_work E C cost x y ⟨n, (reach_true E n x y).mp h⟩
    dsimp only
    omega
  · dsimp only
    omega

end SortingAdversary.Optimal.ScaleWalksWork
