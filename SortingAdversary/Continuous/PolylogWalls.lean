import SortingAdversary.Continuous.PolylogGraph
import SortingAdversary.Continuous.PolylogRouting
import SortingAdversary.Continuous.FeasibleRank
import SortingAdversary.Continuous.RationalState

/-!
# Sparse wall updates implement the reference normalization

The feasible projection onto a coordinate is its open canonical interval.
Consequently normalized positive-width systems with the same arcs and feasible
assignments are equal. This gives literal equality to the controller's dense
normalization, including on future calls that inspect the stored walls.

A one-sided threshold clips one cone. Fixing a coordinate clips both strict
cones and resets that coordinate at its new node. Repeated vertices in the
cone enumerations are harmless.
-/

namespace SortingAdversary.Continuous.PolylogWalls

open FiniteAveraging TreeState OrderRegion PolylogGraph

variable {n m : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem system_ext (D E : System (Fin n) K) (hl : D.lower = E.lower)
    (hu : D.upper = E.upper) (he : D.edge = E.edge) : D = E := by
  cases D; cases E; simp_all

/-- Uniqueness of the canonical endpoints of a nonempty order region. -/
theorem canonical_unique (D E : System (Fin n) K) (hD : Normalized D) (hE : Normalized E)
    (edges : D.edge = E.edge) (feas : ∀ Y, D.StrictlyFeasible Y ↔ E.StrictlyFeasible Y)
    (Y : Fin n → K) (hy : D.StrictlyFeasible Y)
    (rank : Fin n → Fin m) (hr : ∀ x y, D.edge x y = true → rank x < rank y) : D = E := by
  have ey := (feas Y).mp hy
  have wd (x) := (hy.1 x).1.trans (hy.1 x).2
  have we (x) := (ey.1 x).1.trans (ey.1 x).2
  have bounds (x : Fin n) : D.lower x = E.lower x ∧ D.upper x = E.upper x := by
    have eqI : Set.Ioo (D.lower x) (D.upper x) = Set.Ioo (E.lower x) (E.upper x) := by
      ext c
      change (_ < _ ∧ _ < _) ↔ (_ < _ ∧ _ < _)
      rw [← projection_eq_interval D hD wd rank hr x c,
        ← projection_eq_interval E hE we rank (by simpa [← edges] using hr) x c]
      exact exists_congr fun X => and_congr_left fun _ => feas X
    have f := (Set.Ioo_subset_Ioo_iff (wd x)).mp eqI.subset
    have b := (Set.Ioo_subset_Ioo_iff (we x)).mp eqI.symm.subset
    exact ⟨le_antisymm b.1 f.1, le_antisymm f.2 b.2⟩
  exact system_ext D E (funext fun x => (bounds x).1) (funext fun x => (bounds x).2) edges

/-- The actual `graphRank`/normalization pass can be replaced by any exact
local canonicalization. Both real positivity and the rank are proof data. -/
theorem eq_reference (raw sparse : System (Fin n) ℚ) (edges : sparse.edge = raw.edge)
    (normalized : Normalized sparse)
    (feas : ∀ Y, sparse.StrictlyFeasible Y ↔ raw.StrictlyFeasible Y)
    (X : Fin n → ℝ) (hx : raw.toReal.StrictlyFeasible X) :
    sparse = OrderRegion.normalize raw (rankOrder (GraphOrder.graphRank raw)) := by
  obtain ⟨r, rb, hr⟩ := rank_of_feasible raw.toReal hx
  let rank (x : Fin n) : Fin n := ⟨r x, rb x⟩
  let order := rankOrder (GraphOrder.graphRank raw)
  let E := OrderRegion.normalize raw order
  have en : Normalized E := normalize_rankOrder_normalized _ _ (GraphOrder.graphRank_strict raw r hr)
  have ee : E.edge = raw.edge := normalize_edge _ _
  have hrE : ∀ x y, E.edge x y = true → rank x < rank y := by
    intro x y he; exact hr x y (by rwa [ee] at he)
  have ER : E.toReal.StrictlyFeasible X := by
    rw [show E.toReal = OrderRegion.normalize raw.toReal order from TreeState.normalizeSystem_toReal _ _]
    exact (normalize_feasible_iff _ _ _).mpr hx
  have widths (x : Fin n) : E.lower x < E.upper x :=
    (Rat.cast_lt (K := ℝ)).mp ((ER.1 x).1.trans (ER.1 x).2)
  obtain ⟨Y, hy⟩ := feasible_of_normalized E en widths rank hrE
  have same (Y) : sparse.StrictlyFeasible Y ↔ E.StrictlyFeasible Y :=
    (feas Y).trans (normalize_feasible_iff raw order Y).symm
  exact canonical_unique sparse E normalized en (edges.trans ee.symm) same Y ((same Y).mpr hy)
    rank (fun x y he => hr x y (by rwa [edges] at he))

theorem insert_eq_reference (D : System (Fin n) ℚ) (hD : Normalized D)
    (a b : Fin n) (down up : List (Fin n)) (hd : ∀ y, y ∈ down ↔ Reaches D b y)
    (hu : ∀ y, y ∈ up ↔ Reaches D y a) (X : Fin n → ℝ)
    (hX : (addArc D a b).toReal.StrictlyFeasible X) :
    let raw := addArc D a b
    insert D a b down up = OrderRegion.normalize raw (rankOrder (GraphOrder.graphRank raw)) :=
  eq_reference _ _ rfl (insert_normalized _ hD _ _ _ _ hd hu)
    (insert_feasible_iff _ _ _ _ _ (fun y => (hd y).mp) (fun y => (hu y).mp)) _ hX

/-- Lower walls of `down` and upper walls of `up` are clipped at `c`. -/
def clip (D : System (Fin n) K) (down up : List (Fin n)) (c : K) : System (Fin n) K where
  lower y := if y ∈ down then max (D.lower y) c else D.lower y
  upper y := if y ∈ up then min (D.upper y) c else D.upper y
  edge := D.edge

omit [Field K] [IsStrictOrderedRing K] in
private theorem clip_normalized (D : System (Fin n) K) (hD : Normalized D)
    (down up : List (Fin n)) (c : K)
    (hd : ∀ x y, D.edge x y = true → x ∈ down → y ∈ down)
    (hu : ∀ x y, D.edge x y = true → y ∈ up → x ∈ up) : Normalized (clip D down up c) := by
  intro x y e
  obtain ⟨hl, hr⟩ := hD x y e
  constructor
  · by_cases hx : x ∈ down
    · simpa [clip, hx, hd x y e hx] using max_le_max_right c hl
    · by_cases hy : y ∈ down <;> simp [clip, hx, hy, hl.trans (le_max_left _ _), hl]
  · by_cases hy : y ∈ up
    · simpa [clip, hy, hu x y e hy] using min_le_min_right c hr
    · by_cases hx : x ∈ up <;> simp [clip, hx, hy, (min_le_left _ _).trans hr, hr]

omit [Field K] [IsStrictOrderedRing K] in
private theorem clip_feasible (D : System (Fin n) K) (down up : List (Fin n)) (c : K)
    (Y : Fin n → K) :
    (clip D down up c).StrictlyFeasible Y ↔
      D.StrictlyFeasible Y ∧ (∀ y ∈ down, c < Y y) ∧ ∀ y ∈ up, Y y < c := by
  constructor
  · intro hf
    have hl (y) : D.lower y < Y y ∧ (y ∈ down → c < Y y) := by
      have h := (hf.1 y).1
      by_cases hy : y ∈ down <;> simp_all [clip]
    have hr (y) : Y y < D.upper y ∧ (y ∈ up → Y y < c) := by
      have h := (hf.1 y).2
      by_cases hy : y ∈ up <;> simp_all [clip]
    exact ⟨⟨fun y => ⟨(hl y).1,(hr y).1⟩,hf.2⟩,fun y => (hl y).2,fun y => (hr y).2⟩
  · rintro ⟨hf, hd, hu⟩
    refine ⟨fun y => ⟨?_,?_⟩, hf.2⟩
    · by_cases hy : y ∈ down <;> simp_all [clip, (hf.1 y).1]
    · by_cases hy : y ∈ up <;> simp_all [clip, (hf.1 y).2]

omit [Field K] [IsStrictOrderedRing K] in
private theorem reach_le (D : System (Fin n) K) {Y : Fin n → K} (hY : D.StrictlyFeasible Y)
    {a b : Fin n} (h : Reaches D a b) : Y a ≤ Y b := by
  induction h with
  | refl => rfl
  | tail _ he ih => exact ih.trans (hY.2 _ _ he).le

omit [Field K] [IsStrictOrderedRing K] in
private theorem reach_lt (D : System (Fin n) K) {Y : Fin n → K} (hY : D.StrictlyFeasible Y)
    {a b : Fin n} (h : Reaches D a b) (hne : a ≠ b) : Y a < Y b := by
  cases h with
  | refl => exact (hne rfl).elim
  | tail p e => exact (reach_le D hY p).trans_lt (hY.2 _ _ e)

theorem above_eq_reference (D : System (Fin n) ℚ) (hD : Normalized D)
    (x : Fin n) (down : List (Fin n)) (hd : ∀ y, y ∈ down ↔ Reaches D x y) (c : ℚ)
    (X : Fin n → ℝ) (hx : (boundAbove D x c).toReal.StrictlyFeasible X) :
    let raw := boundAbove D x c
    clip D down [] c = OrderRegion.normalize raw (rankOrder (GraphOrder.graphRank raw)) := by
  apply eq_reference (boundAbove D x c) (clip D down [] c) rfl _ _ X hx
  · apply clip_normalized _ hD
    · intro a b e ha; exact (hd b).mpr (((hd a).mp ha).tail e)
    · simp
  · intro Y
    rw [clip_feasible, boundAbove_feasible_iff]
    simp only [List.not_mem_nil, false_implies, implies_true, and_true]
    exact and_congr_right fun h => ⟨fun a => a x ((hd x).mpr .refl),
      fun a y hy => a.trans_le (reach_le D h ((hd y).mp hy))⟩

theorem below_eq_reference (D : System (Fin n) ℚ) (hD : Normalized D)
    (x : Fin n) (up : List (Fin n)) (hu : ∀ y, y ∈ up ↔ Reaches D y x) (c : ℚ)
    (X : Fin n → ℝ) (hx : (boundBelow D x c).toReal.StrictlyFeasible X) :
    let raw := boundBelow D x c
    clip D [] up c = OrderRegion.normalize raw (rankOrder (GraphOrder.graphRank raw)) := by
  apply eq_reference (boundBelow D x c) (clip D [] up c) rfl _ _ X hx
  · apply clip_normalized _ hD
    · simp
    · intro a b e hb; exact (hu a).mpr (((hu b).mp hb).head e)
  · intro Y
    rw [clip_feasible, boundBelow_feasible_iff]
    simp only [List.not_mem_nil, false_implies, implies_true, true_and]
    exact and_congr_right fun h => ⟨fun a => a x ((hu x).mpr .refl),
      fun a y hy => (reach_le D h ((hu y).mp hy)).trans_lt a⟩

/-- Delete all incident arcs and give `x` a unit interval. -/
def isolate (D : System (Fin n) K) (x : Fin n) : System (Fin n) K where
  lower y := if y = x then 0 else D.lower y
  upper y := if y = x then 1 else D.upper y
  edge := (resetCoordinate D x 0).edge

omit [IsStrictOrderedRing K] in
private theorem isolate_edge (D : System (Fin n) K) (x a b : Fin n) :
    (isolate D x).edge a b = true ↔ a ≠ x ∧ b ≠ x ∧ D.edge a b = true := by
  by_cases ha : a = x <;> by_cases hb : b = x <;> simp [isolate, resetCoordinate, ha, hb]

omit [IsStrictOrderedRing K] in
private theorem isolate_norm (D : System (Fin n) K) (hD : Normalized D) (x : Fin n) :
    Normalized (isolate D x) := by
  intro a b e
  obtain ⟨ha,hb,he⟩ := (isolate_edge _ _ _ _).mp e
  simpa [isolate, ha, hb] using hD a b he

/-- The lists include their root, which is excluded from both clips after it
receives its new unit interval. -/
def fixAt (D : System (Fin n) K) (x : Fin n) (c : K) (down up : List (Fin n)) :
    System (Fin n) K := clip (isolate D x) (down.filter (· ≠ x)) (up.filter (· ≠ x)) c

theorem fix_eq_reference (D : System (Fin n) ℚ) (hD : Normalized D) (x : Fin n) (c : ℚ)
    (hc : D.lower x < c ∧ c < D.upper x) (loop : D.edge x x = false)
    (down up : List (Fin n)) (hd : ∀ y, y ∈ down ↔ Reaches D x y)
    (hu : ∀ y, y ∈ up ↔ Reaches D y x)
    (X : Fin n → ℝ) (hx : (resetCoordinate D x c).toReal.StrictlyFeasible X) :
    let raw := resetCoordinate D x c
    fixAt D x c down up = OrderRegion.normalize raw (rankOrder (GraphOrder.graphRank raw)) := by
  apply eq_reference (resetCoordinate D x c) (fixAt D x c down up) rfl _ _ X hx
  · apply clip_normalized _ (isolate_norm _ hD _)
    · intro a b he ha
      obtain ⟨_,hn,e⟩ := (isolate_edge _ _ _ _).mp he
      simp only [List.mem_filter, decide_eq_true_eq] at ha ⊢
      exact ⟨(hd b).mpr (((hd a).mp ha.1).tail e),hn⟩
    · intro a b he hb
      obtain ⟨hn,_,e⟩ := (isolate_edge _ _ _ _).mp he
      simp only [List.mem_filter, decide_eq_true_eq] at hb ⊢
      exact ⟨(hu a).mpr (((hu b).mp hb.1).head e),hn⟩
  · intro Y
    rw [fixAt, clip_feasible, resetCoordinate_feasible_iff D x c loop hc]
    simp only [List.mem_filter, decide_eq_true_eq, and_imp]
    constructor
    · rintro ⟨hi, lo, up'⟩
      refine ⟨by simpa [isolate] using hi.1 x, ?_⟩
      constructor
      · intro y
        by_cases he : y = x
        · simpa [he] using hc
        · simpa [isolate, he] using hi.1 y
      · intro a b he
        by_cases ha : a = x
        · subst a
          have hb : b ≠ x := by intro h; subst b; simp [loop] at he
          simpa [hb] using lo b ((hd b).mpr (.single he)) hb
        · by_cases hb : b = x
          · subst b; simpa [ha] using up' a ((hu a).mpr (.single he)) ha
          · simpa [ha,hb] using hi.2 a b ((isolate_edge _ _ _ _).mpr ⟨ha,hb,he⟩)
    · rintro ⟨unit, hf⟩
      constructor
      · constructor
        · intro y
          by_cases he : y = x
          · simpa [isolate,he] using unit
          · simpa [isolate,he] using hf.1 y
        · intro a b he
          obtain ⟨ha,hb,e⟩ := (isolate_edge _ _ _ _).mp he
          simpa [ha,hb] using hf.2 _ _ e
      · constructor
        · intro y hy he
          simpa [he] using reach_lt D hf ((hd y).mp hy) he.symm
        · intro y hy he
          simpa [he] using reach_lt D hf ((hu y).mp hy) he

section Tables

open PolylogRouting (Table)
open SortingAdversary.Optimal.PrimitiveWork (Result)

/-- Update the listed cells of a persistent table, with measured reads,
comparisons and writes. Repeated occurrences cost work but preserve the
result of an idempotent operation. -/
def edit (f : α → Result α) (t : Table α h) : List (Fin n) → Result (Table α h)
  | [] => ⟨t, 1⟩
  | x :: xs =>
    let a := t.get x.val
    let b := f a.value
    let w := t.put x.val b.value
    let r := edit f w.value xs
    ⟨r.value, a.work + b.work + w.work + r.work + 3⟩

theorem edit_work (f : α → Result α) (B : ℕ) (hf : ∀ a, (f a).work ≤ B)
    (t : Table α h) (xs : List (Fin n)) :
    (edit f t xs).work ≤ xs.length*(9*h+B+5) + 1 := by
  induction xs generalizing t with
  | nil => simp [edit]
  | cons x xs ih =>
    have := hf (t.get x.val).value
    simp only [edit, Table.get_work, Table.put_work, List.length_cons, Nat.add_mul, one_mul]
    have := ih (t.put x.val (f (t.get x.val).value).value).value
    omega

/-- The table has `2^h` entries. Its ghost decoding can identify different
representations of the same scalar. -/
theorem edit_value (f : α → Result α) (decode : α → β) (g : β → β)
    (spec : ∀ a, decode (f a).value = g (decode a)) (idem : ∀ b, g (g b) = g b)
    (capacity : n ≤ 2^h) (t : Table α h) (xs : List (Fin n)) (y : Fin n) :
    decode ((edit f t xs).value.get y.val).value =
      if y ∈ xs then g (decode (t.get y.val).value) else decode (t.get y.val).value := by
  induction xs generalizing t with
  | nil => simp [edit]
  | cons x xs ih =>
    simp only [edit, ih, Table.get_put _ _ _ _ (x.isLt.trans_le capacity) (y.isLt.trans_le capacity)]
    by_cases eq : y = x
    · subst y; by_cases hx : x ∈ xs <;> simp [hx, spec, idem]
    · have ne : y.val ≠ x.val := fun e => eq (Fin.ext e)
      simp [eq, ne]

/-- A counted maximum/minimum on reference cells. The two physical tables
hold lower and upper wall references separately. -/
def clamp (lt : α → α → Result Bool) (raise : Bool) (c a : α) : Result α :=
  let test := if raise then lt a c else lt c a
  ⟨if test.value then c else a, test.work + 2⟩

theorem clamp_spec (lt : α → α → Result Bool) (decode : α → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    (raise : Bool) (c a : α) : decode (clamp lt raise c a).value =
      if raise then max (decode a) (decode c) else min (decode a) (decode c) := by
  cases raise <;> simp only [clamp, Bool.false_eq_true, if_false, if_true, hc] <;> split
  all_goals simp_all [le_of_lt, le_of_not_gt]

theorem clipTable_value (lt : α → α → Result Bool) (decode : α → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b) (raise : Bool) (c : α)
    (cap : n ≤ 2^h) (t : Table α h) (cone : List (Fin n)) (y : Fin n) :
    let old := decode (t.get y.val).value
    decode ((edit (clamp lt raise c) t cone).value.get y.val).value =
      if y ∈ cone then (if raise then max old (decode c) else min old (decode c)) else old := by
  refine edit_value (clamp lt raise c) decode
    (fun b => if raise then max b (decode c) else min b (decode c))
    (clamp_spec lt decode hc raise c) ?_ cap t cone y
  intro b
  cases raise <;> simp

theorem clipTable_work (lt : α → α → Result Bool) (B : ℕ)
    (hc : ∀ a b, (lt a b).work ≤ B) (raise : Bool) (c : α) (t : Table α h)
    (cone : List (Fin n)) :
    (edit (clamp lt raise c) t cone).work ≤ cone.length * (9*h+B+7)+1 := by
  have hb (a : α) : (clamp lt raise c a).work ≤ B+2 := by
    cases raise <;> simp [clamp, hc]
  simpa only [Nat.add_assoc] using edit_work _ (B+2) hb t cone

end Tables

end SortingAdversary.Continuous.PolylogWalls
