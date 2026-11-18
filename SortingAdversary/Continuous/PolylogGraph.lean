import SortingAdversary.Continuous.TreeRouting
import SortingAdversary.Continuous.Normalization
import SortingAdversary.Optimal.GraphBalls

/-!
# Local propagation after inserting a comparison arc

Starting with normalized walls, the insertion of `a → b` requires only two
old directed cones. We enumerate them from adjacency lists. Repeated visits
are harmless: the wall updates are maxima and minima with a single constant.
The traversal need not allocate an array indexed by all labels or clear a
visited set. Its work bound depends on the degree and height alone.
-/

namespace SortingAdversary.Continuous.PolylogGraph

open FiniteAveraging OrderRegion TreeState

variable {V : Type*}

/-- Visit the endpoints of walks of length at most the budget, with multiplicity. -/
def visit (next : V → List V) : ℕ → V → List V
  | 0, x => [x]
  | h + 1, x => x :: (next x).flatMap (visit next h)

theorem self_mem_visit (next : V → List V) (h : ℕ) (x : V) : x ∈ visit next h x := by
  cases h <;> simp [visit]

theorem mem_visit_mono (next : V → List V) (h : ℕ) {x y : V}
    (hm : y ∈ visit next h x) : y ∈ visit next (h+1) x := by
  induction h generalizing x with
  | zero =>
    have hy : y = x := by simpa [visit] using hm
    subst y
    exact self_mem_visit _ _ _
  | succ h ih =>
    rcases List.mem_cons.mp hm with rfl | ht
    · exact self_mem_visit _ _ _
    · obtain ⟨w, hw, hy⟩ := List.mem_flatMap.mp ht
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨w, hw, ih hy⟩)

theorem mem_visit_reaches (next : V → List V) (h : ℕ) {x y : V}
    (hm : y ∈ visit next h x) :
    Relation.ReflTransGen (fun u v => v ∈ next u) x y := by
  induction h generalizing x with
  | zero =>
    have hy : y = x := by simpa [visit] using hm
    subst y
    exact .refl
  | succ h ih =>
    rcases List.mem_cons.mp hm with rfl | ht
    · exact .refl
    · obtain ⟨w, hw, hy⟩ := List.mem_flatMap.mp ht
      exact (ih hy).head hw

/-- A strictly decreasing natural rank supplies fuel in the traversal direction. -/
theorem reaches_mem_visit (next : V → List V) (rank : V → ℕ)
    (hr : ∀ u v, v ∈ next u → rank v < rank u) {x y : V}
    (reach : Relation.ReflTransGen (fun u v => v ∈ next u) x y)
    (h : ℕ) (hx : rank x ≤ h) : y ∈ visit next h x := by
  induction h generalizing x with
  | zero =>
    cases reach using Relation.ReflTransGen.head_induction_on with
    | refl => exact self_mem_visit _ _ _
    | @head a b hab _ _ => have := hr _ _ hab; omega
  | succ h ih =>
    cases reach using Relation.ReflTransGen.head_induction_on with
    | refl => exact self_mem_visit _ _ _
    | @head a b hab hby _ =>
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨b, hab, ih hby (by have := hr _ _ hab; omega)⟩)

/-- Number of list cells emitted. The recursion performs one adjacency lookup
per internal visit. Each traversed adjacency-list entry gives one child visit. -/
theorem visit_length_le (next : V → List V) (d : ℕ) (hd : ∀ v, (next v).length ≤ d)
    (h : ℕ) (x : V) : (visit next h x).length ≤ (d + 1) ^ h := by
  induction h generalizing x with
  | zero => simp [visit]
  | succ h ih =>
    have hsum (xs : List V) :
        (xs.flatMap (visit next h)).length ≤ xs.length * (d + 1) ^ h := by
      induction xs with
      | nil => simp
      | cons y ys hy =>
        simpa [List.flatMap_cons, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using Nat.add_le_add (ih y) hy
    have hb := (hsum (next x)).trans (Nat.mul_le_mul_right _ (hd x))
    have hp : 1 ≤ (d + 1) ^ h := Nat.one_le_pow _ _ (by omega)
    simp only [visit, List.length_cons, pow_succ, Nat.mul_add, Nat.mul_one]
    rw [Nat.mul_comm ((d + 1) ^ h) d]
    omega

/-- Accumulator traversal with a counter. We charge one unit for an emitted
vertex, one for reading its adjacency row at positive depth, and one for
each child dispatch. The accumulator shares its tail across recursive calls. -/
def emit (next : V → List V) : ℕ → V → List V × ℕ → List V × ℕ
  | 0, x, (out, work) => (x :: out, work + 1)
  | h + 1, x, tail =>
    let r := (next x).foldr (fun y acc =>
      emit next h y (acc.1, acc.2 + 1)) tail
    (x :: r.1, r.2 + 2)

theorem emit_spec (next : V → List V) (h : ℕ) (x : V) (out : List V) (work : ℕ) :
    (emit next h x (out, work)).1 = visit next h x ++ out ∧
      (emit next h x (out, work)).2 ≤ work + 3 * (visit next h x).length - 1 := by
  induction h generalizing x out work with
  | zero => simp [emit, visit]
  | succ h ih =>
    let step := fun (y : V) (acc : List V × ℕ) => emit next h y (acc.1, acc.2 + 1)
    have children (ys : List V) :
        (ys.foldr step (out, work)).1 = ys.flatMap (visit next h) ++ out ∧
        (ys.foldr step (out, work)).2 ≤ work + 3 * (ys.flatMap (visit next h)).length := by
      induction ys with
      | nil => simp
      | cons y ys hy =>
        let acc := ys.foldr step (out, work)
        obtain ⟨hv, hw⟩ := ih y acc.1 (acc.2 + 1)
        have ha : acc.2 ≤ work + 3 * (ys.flatMap (visit next h)).length := hy.2
        change (emit next h y (acc.1, acc.2+1)).1 = _ ∧
          (emit next h y (acc.1, acc.2+1)).2 ≤ _
        simp only [List.flatMap_cons, List.length_append, List.append_assoc]
        refine ⟨by rw [hv, show acc.1 = _ from hy.1], by omega⟩
    obtain ⟨hv, hw⟩ := children (next x)
    change x :: ((next x).foldr step (out, work)).1 = _ ∧
      ((next x).foldr step (out, work)).2 + 2 ≤ _
    simp only [visit, List.cons_append, List.length_cons, hv]
    exact ⟨trivial, by omega⟩

theorem emit_work_le (next : V → List V) (d : ℕ) (hd : ∀ v, (next v).length ≤ d)
    (h : ℕ) (x : V) : (emit next h x ([], 0)).2 ≤ 3 * (d+1)^h := by
  have hw := (emit_spec next h x [] 0).2
  have hl := visit_length_le next d hd h x
  omega

/-- Any stored adjacency lists enumerating exactly the proper undirected
neighbors compute the same retained ball as the original enclosure. -/
theorem visit_iff_mem_ball [Fintype V] [DecidableEq V] (E : V → V → Bool)
    (next : V → List V)
    (hn : ∀ x y, y ∈ next x ↔ y ∈ Optimal.GraphBalls.neighbors E x)
    (x y : V) (h : ℕ) : y ∈ visit next h x ↔ y ∈ Optimal.GraphBalls.ball E x h := by
  induction h generalizing x with
  | zero => simp [visit, Optimal.GraphBalls.ball]
  | succ h ih =>
    rw [Optimal.GraphBalls.mem_ball_succ]
    constructor
    · intro hy
      rcases List.mem_cons.mp hy with rfl | hm
      · exact ⟨y, by simp [Optimal.GraphBalls.closedNeighbors],
          Optimal.GraphBalls.center_mem_ball E y h⟩
      · obtain ⟨w, hw, hy⟩ := List.mem_flatMap.mp hm
        exact ⟨w, Finset.mem_insert_of_mem ((hn x w).mp hw), (ih w).mp hy⟩
    · rintro ⟨w, hw, hy⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact mem_visit_mono _ _ ((ih w).mpr hy)
      · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨w, (hn x w).mpr hw, (ih w).mpr hy⟩)

section Insert

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Pointwise reading of the sparse updates on the descendant and ancestor
lists. `down` contains the descendants of `b`, and `up` the ancestors of `a`,
including both roots. -/
def insert (D : System (Fin n) K) (a b : Fin n) (down up : List (Fin n)) :
    System (Fin n) K where
  edge := (addArc D a b).edge
  lower x := if x ∈ down then max (D.lower x) (D.lower a) else D.lower x
  upper x := if x ∈ up then min (D.upper x) (D.upper b) else D.upper x

omit [Field K] [IsStrictOrderedRing K] in
theorem insert_normalized (D : System (Fin n) K) (hD : Normalized D)
    (a b : Fin n) (down up : List (Fin n))
    (hd : ∀ x, x ∈ down ↔ Reaches D b x) (hu : ∀ x, x ∈ up ↔ Reaches D x a) :
    Normalized (insert D a b down up) := by
  intro x y he
  change (addArc D a b).edge x y = true at he
  rcases (show D.edge x y = true ∨ (x = a ∧ y = b) by simpa [addArc] using he)
    with h | ⟨rfl, rfl⟩
  · obtain ⟨hl, hr⟩ := hD x y h
    constructor
    · by_cases hx : x ∈ down
      · have hy := (hd y).mpr (((hd x).mp hx).tail h)
        simpa [insert, hx, hy] using max_le_max_right (D.lower a) hl
      · simp only [insert, if_neg hx]
        split <;> first | exact hl | exact hl.trans (le_max_left _ _)
    · by_cases hy : y ∈ up
      · have hx := (hu x).mpr (((hu y).mp hy).head h)
        simpa [insert, hx, hy] using min_le_min_right (D.upper b) hr
      · simp only [insert, if_neg hy]
        split <;> first | exact hr | exact (min_le_left _ _).trans hr
  · have hby := (hd y).mpr Relation.ReflTransGen.refl
    have hax := (hu x).mpr Relation.ReflTransGen.refl
    simp [insert, hby, hax]

theorem insert_feasible_iff (D : System (Fin n) K) (a b : Fin n)
    (down up : List (Fin n)) (hd : ∀ x, x ∈ down → Reaches D b x)
    (hu : ∀ x, x ∈ up → Reaches D x a) (Y : Fin n → K) :
    (insert D a b down up).StrictlyFeasible Y ↔ (addArc D a b).StrictlyFeasible Y := by
  constructor
  · intro h
    refine ⟨fun x => ⟨?_, ?_⟩, h.2⟩
    · have hl := (h.1 x).1
      simp only [insert] at hl
      split at hl
      · exact (max_lt_iff.mp hl).1
      · exact hl
    · have hu' := (h.1 x).2
      simp only [insert] at hu'
      split at hu'
      · exact (lt_min_iff.mp hu').1
      · exact hu'
  · intro h
    obtain ⟨hD, hab⟩ := (addArc_feasible_iff D a b Y).mp h
    have hr {x y : Fin n} (reach : Reaches D x y) : Y x ≤ Y y := by
      induction reach with
      | refl => rfl
      | tail _ hxy ih => exact ih.trans (hD.2 _ _ hxy).le
    refine ⟨fun x => ⟨?_, ?_⟩, h.2⟩
    · simp only [insert]
      split
      · rename_i hx
        exact max_lt (hD.1 x).1 (((hD.1 a).1.trans hab).trans_le (hr (hd x hx)))
      · exact (hD.1 x).1
    · simp only [insert]
      split
      · rename_i hx
        exact lt_min (hD.1 x).2 ((hr (hu x hx)).trans_lt (hab.trans (hD.1 b).2))
      · exact (hD.1 x).2

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The bounded outgoing traversal computes the reflexive descendant cone
of the old graph. The input rank need not be computed during the search. -/
theorem descendants_exact (D : System (Fin n) K) (next : Fin n → List (Fin n))
    (hn : ∀ x y, y ∈ next x ↔ D.edge x y = true) (rank : Fin n → ℕ)
    (hr : ∀ x y, D.edge x y = true → rank x < rank y) (H : ℕ)
    (hH : ∀ x, rank x < H) (x y : Fin n) :
    y ∈ visit next H x ↔ Reaches D x y := by
  constructor
  · intro hy
    exact Relation.ReflTransGen.mono (fun u v h => (hn u v).mp h) x y
      (mem_visit_reaches next H hy)
  · intro hy
    apply reaches_mem_visit next (fun z => H - rank z) (fun u v h => ?_)
      (Relation.ReflTransGen.mono (fun u v h => (hn u v).mpr h) x y hy) H (Nat.sub_le _ _)
    have := hr u v ((hn u v).mp h)
    have := hH v
    omega

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem ancestors_exact (D : System (Fin n) K) (prev : Fin n → List (Fin n))
    (hp : ∀ x y, y ∈ prev x ↔ D.edge y x = true) (rank : Fin n → ℕ)
    (hr : ∀ x y, D.edge x y = true → rank x < rank y) (H : ℕ)
    (hH : ∀ x, rank x < H) (x y : Fin n) :
    y ∈ visit prev H x ↔ Reaches D y x := by
  constructor
  · intro hy
    have hh := mem_visit_reaches prev H hy
    clear hy
    induction hh with
    | refl => exact .refl
    | @tail v w _ he ih => exact ih.head ((hp v w).mp he)
  · intro hy
    apply reaches_mem_visit prev rank (fun u v h => hr v u ((hp u v).mp h)) _ H (hH x).le
    induction hy with
    | refl => exact .refl
    | @tail v w _ he ih => exact ih.head ((hp w v).mpr he)

/-- Local normalization of an inserted arc, using the actual two traversals. -/
theorem insert_from_lists (D : System (Fin n) K) (hD : Normalized D)
    (next prev : Fin n → List (Fin n))
    (hn : ∀ x y, y ∈ next x ↔ D.edge x y = true)
    (hp : ∀ x y, y ∈ prev x ↔ D.edge y x = true)
    (rank : Fin n → ℕ) (hr : ∀ x y, D.edge x y = true → rank x < rank y)
    (H : ℕ) (hH : ∀ x, rank x < H) (a b : Fin n) :
    let updated := insert D a b (emit next H b ([], 0)).1 (emit prev H a ([], 0)).1
    Normalized updated ∧
      ∀ Y, updated.StrictlyFeasible Y ↔ (addArc D a b).StrictlyFeasible Y := by
  simp only [(emit_spec next H b [] 0).1, (emit_spec prev H a [] 0).1, List.append_nil]
  have hd := descendants_exact D next hn rank hr H hH b
  have hu := ancestors_exact D prev hp rank hr H hH a
  exact ⟨insert_normalized D hD a b _ _ hd hu,
    insert_feasible_iff D a b _ _ (fun x => (hd x).mp) (fun x => (hu x).mp)⟩

end Insert
end SortingAdversary.Continuous.PolylogGraph
