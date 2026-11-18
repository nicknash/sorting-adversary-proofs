import SortingAdversary.Continuous.PolylogWalls
import SortingAdversary.Continuous.PolylogBits

/-!
# Executing wall changes in the stored tables

The only inputs read by a mutation are the old wall references of the two arc
endpoints (when inserting an arc) and adjacency rows in the affected cones.
A fix overwrites its own two cells *after* clipping, so duplicate visits and
the root entries require no filtering.
-/

namespace SortingAdversary.Continuous.PolylogWallTables

open FiniteAveraging TreeState OrderRegion PolylogGraph PolylogWalls
open PolylogRouting (Table)
open SortingAdversary.Optimal.PrimitiveWork (Result)

variable {α : Type} {n h : ℕ}

abbrev Rows (n h : ℕ) := Table (List (Fin n)) h

/-- Stack traversal with charged random accesses to actual stored lists. -/
def enumerate (rows : Rows n h) : ℕ → Fin n → List (Fin n) × ℕ → List (Fin n) × ℕ
  | 0, x, (out, w) => (x :: out, w + 3)
  | H+1, x, acc =>
    let row := rows.get x.val
    let r := row.value.foldr (fun y t => enumerate rows H y t) acc
    (x :: r.1, r.2 + row.work + 4)

theorem enumerate_spec (rows : Rows n h) (H : ℕ) (x : Fin n) (out : List (Fin n)) (w : ℕ) :
    let xs := visit (fun y : Fin n => (rows.get y.val).value) H x
    (enumerate rows H x (out,w)).1 = xs ++ out ∧
      (enumerate rows H x (out,w)).2 ≤ w + xs.length * (4*h+5) := by
  induction H generalizing x out w with
  | zero => simp [enumerate, visit]
  | succ H ih =>
    let children (y : Fin n) := visit (fun z : Fin n => (rows.get z.val).value) H y
    have fold (ys : List (Fin n)) :
        let r := ys.foldr (fun y t => enumerate rows H y t) (out,w)
        r.1 = ys.flatMap children ++ out ∧
          r.2 ≤ w + (ys.flatMap children).length*(4*h+5) := by
      induction ys with
      | nil => simp
      | cons y ys hy =>
        let acc := ys.foldr (fun z t => enumerate rows H z t) (out,w)
        obtain ⟨eq, cost⟩ := ih y acc.1 acc.2
        change (enumerate rows H y acc).1 = _ ∧ (enumerate rows H y acc).2 ≤ _
        change (enumerate rows H y acc).2 ≤ acc.2 + (children y).length * (4*h+5) at cost
        have tail : acc.2 ≤ _ := hy.2
        simp only [List.flatMap_cons, List.length_append, Nat.add_mul, List.append_assoc]
        exact ⟨by rw [eq, show acc.1 = _ from hy.1], by omega⟩
    let ys := (rows.get x.val).value
    have hf := fold ys
    change x :: _ = _ ∧ _ ≤ _
    simp only [enumerate, visit, Table.get_work, List.cons_append, List.length_cons,
      Nat.add_mul, one_mul]
    refine ⟨congrArg (x :: ·) hf.1, ?_⟩
    apply (Nat.add_le_add_right (Nat.add_le_add_right hf.2 (4*h+1)) 4).trans
    let m := (ys.flatMap children).length * (4*h+5)
    change w + m + (4*h+1) + 4 ≤ w + (m + (4*h+5))
    omega

structure Walls (α : Type) (h : ℕ) where
  lower : Table α h
  upper : Table α h

/-- `fix` moves a free vertex to a child; its new coordinate has unit bounds. -/
inductive Change (α : Type) (n : ℕ) where
  | arc (a b : Fin n)
  | above (x : Fin n) (c : α)
  | below (x : Fin n) (c : α)
  | fix (x : Fin n) (c : α)
  | unchanged

def raw (decode : α → ℚ) (D : System (Fin n) ℚ) : Change α n → System (Fin n) ℚ
  | .arc a b => addArc D a b
  | .above x c => boundAbove D x (decode c)
  | .below x c => boundBelow D x (decode c)
  | .fix x c => resetCoordinate D x (decode c)
  | .unchanged => D

abbrev Cut (α : Type) (n : ℕ) := Option (Fin n × α)

structure Plan (α : Type) (n : ℕ) where
  down : Cut α n
  up : Cut α n
  reset : Option (Fin n)

def plan (w : Walls α h) : Change α n → Result (Plan α n)
  | .arc a b =>
    let l := w.lower.get a.val
    let u := w.upper.get b.val
    ⟨⟨some (b,l.value),some (a,u.value),none⟩,l.work + u.work + 4⟩
  | .above x c => ⟨⟨some (x,c),none,none⟩,3⟩
  | .below x c => ⟨⟨none,some (x,c),none⟩,3⟩
  | .fix x c => ⟨⟨some (x,c),some (x,c),some x⟩,4⟩
  | .unchanged => ⟨⟨none,none,none⟩,1⟩

def side (lt : α → α → Result Bool) (raise : Bool) (rows : Rows n h) (H : ℕ) (t : Table α h)
    (cut : Cut α n) (reset : Option (Fin n)) (unitBound : α) : Result (Table α h) :=
  let sparse : Result (Table α h) := match cut with
    | none => ⟨t, 1⟩
    | some (x,c) =>
      let xs := enumerate rows H x ([],0)
      let r := edit (clamp lt raise c) t xs.1
      ⟨r.value, xs.2 + r.work + 2⟩
  match reset with
  | none => ⟨sparse.value, sparse.work+1⟩
  | some x =>
    let r := sparse.value.put x.val unitBound
    ⟨r.value, sparse.work + r.work + 2⟩

def update (lt : α → α → Result Bool) (next prev : Rows n h) (H : ℕ) (zero one : α)
    (w : Walls α h) (op : Change α n) : Result (Walls α h) :=
  let p := plan w op
  let l := side lt true next H w.lower p.value.down p.value.reset zero
  let u := side lt false prev H w.upper p.value.up p.value.reset one
  ⟨⟨l.value,u.value⟩, p.work + l.work + u.work + 3⟩

private def sideBudget (h d H B : ℕ) := (d+1)^H * (13*h+B+12) + 5*h + 6

theorem side_work (lt : α → α → Result Bool) (B : ℕ) (hc : ∀ a b, (lt a b).work ≤ B)
    (rows : Rows n h) (d : ℕ) (hd : ∀ y : Fin n, (rows.get y.val).value.length ≤ d)
    (raise : Bool) (H : ℕ) (t : Table α h) (cut : Cut α n)
    (reset : Option (Fin n)) (unitBound : α) :
    (side lt raise rows H t cut reset unitBound).work ≤ sideBudget h d H B := by
  cases cut with
  | none => cases reset <;> simp [side, sideBudget]; omega
  | some xc =>
    obtain ⟨x,c⟩ := xc
    let xs := enumerate rows H x ([],0)
    let N := (d+1)^H
    have he := enumerate_spec rows H x [] 0
    have len : xs.1.length ≤ N := by
      simpa only [xs, N, he.1, List.append_nil] using visit_length_le _ d hd H x
    have en : xs.2 ≤ N*(4*h+5) := by
      apply he.2.trans
      simpa only [Nat.zero_add] using Nat.mul_le_mul_right _ (visit_length_le _ d hd H x)
    have ew := (clipTable_work lt B hc raise c t xs.1).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ len) 1)
    have dist : N*(13*h+B+12) = N*(4*h+5) + N*(9*h+B+7) := by ring
    change (side lt raise rows H t (some (x,c)) reset unitBound).work ≤ N*(13*h+B+12)+5*h+6
    rw [dist]
    cases reset <;> simp only [side, Table.put_work] <;> dsimp only [xs] at en ew <;> omega

/-- `d` bounds both stored row lengths. `B` is the cost of one exact comparison
of two endpoint references. This includes building the cones and writing all
affected walls, even when the traversal encounters duplicate vertices. -/
theorem update_work (lt : α → α → Result Bool) (B : ℕ) (hc : ∀ a b, (lt a b).work ≤ B)
    (next prev : Rows n h) (d : ℕ)
    (hn : ∀ y : Fin n, (next.get y.val).value.length ≤ d)
    (hp : ∀ y : Fin n, (prev.get y.val).value.length ≤ d)
    (H : ℕ) (zero one : α) (w : Walls α h) (op : Change α n) :
    (update lt next prev H zero one w op).work ≤
      2*((d+1)^H * (13*h+B+12) + 5*h + 6) + 8*h + 9 := by
  have pc : (plan w op).work ≤ 8*h + 6 := by cases op <;> simp [plan]; omega
  have l := side_work lt B hc next d hn true H w.lower (plan w op).value.down (plan w op).value.reset zero
  have u := side_work lt B hc prev d hp false H w.upper (plan w op).value.up (plan w op).value.reset one
  dsimp only [update, sideBudget] at l u ⊢
  omega

def aligned (decode : α → ℚ) (w : Walls α h) (D : System (Fin n) ℚ) : Prop :=
  (∀ y : Fin n, decode (w.lower.get y.val).value = D.lower y) ∧
    ∀ y : Fin n, decode (w.upper.get y.val).value = D.upper y

/-- Two shared uniform tables at initialization. -/
def initial (zero one : α) (h : ℕ) : Walls α h :=
  ⟨Table.fill zero h, Table.fill one h⟩

theorem initial_aligned (decode : α → ℚ) (zero one : α) (hz : decode zero = 0)
    (ho : decode one = 1) (n h : ℕ) :
    aligned decode (initial zero one h) (TreeState.initial n).system := by
  simp [aligned, initial, TreeState.initial, hz, ho]

/-- Dispatch of the reference controller's recorded constraint. -/
def forRecord (r : Routing α) (q : Query n) (a : Answer) : Change α n :=
  match r, a with
  | .coordinates, .less => .arc q.left q.right
  | .coordinates, .greater => .arc q.right q.left
  | .leftFree c, .less => .below q.left c
  | .leftFree c, .greater => .above q.left c
  | .rightFree c, .less => .above q.right c
  | .rightFree c, .greater => .below q.right c
  | .anchors _ _, _ => .unchanged

@[simp] theorem raw_record (decode : α → ℚ) (D : System (Fin n) ℚ) (r : Routing α)
    (q : Query n) (a : Answer) :
    raw decode D (forRecord r q a) =
      recordSystem D (PolylogRouting.decodeRoute decode r) q.left q.right a := by
  cases r <;> cases a <;> rfl

/-- The formula of one side, after applying both its cut and its override. -/
private def atSide (raise : Bool) (decode : α → ℚ) (old : ℚ) (unitBound : α)
    (cut : Cut α n) (reset : Option (Fin n)) (member : Fin n → Prop) [DecidablePred member]
    (y : Fin n) : ℚ :=
  if reset = some y then decode unitBound else
  match cut with
  | none => old
  | some (x,c) =>
    if member x then (if raise then max old (decode c) else min old (decode c)) else old

private theorem side_value (lt : α → α → Result Bool) (decode : α → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    (rows : Rows n h) (raise : Bool) (H : ℕ) (t : Table α h) (cut : Cut α n)
    (reset : Option (Fin n)) (unitBound : α) (cap : n ≤ 2^h) (y : Fin n) :
    decode (((side lt raise rows H t cut reset unitBound).value).get y.val).value =
      atSide raise decode (decode (t.get y.val).value) unitBound cut reset
        (fun x => y ∈ visit (fun z : Fin n => (rows.get z.val).value) H x) y := by
  cases cut with
  | none =>
    cases reset with
    | none => simp [side, atSide]
    | some x =>
      simp only [side, Table.get_put _ _ _ _ (x.isLt.trans_le cap) (y.isLt.trans_le cap), atSide]
      by_cases he : y = x
      · subst y; simp
      · have ne : y.val ≠ x.val := fun e => he (Fin.ext e)
        simp [ne, Ne.symm he]
  | some xc =>
    obtain ⟨x,c⟩ := xc
    let xs := (enumerate rows H x ([],0)).1
    have ex : xs = visit (fun z : Fin n => (rows.get z.val).value) H x := by
      simpa [xs] using (enumerate_spec rows H x [] 0).1
    have cutval := clipTable_value lt decode hc raise c cap t xs y
    cases reset with
    | none =>
      simpa [side, atSide, xs, ex] using cutval
    | some v =>
      simp only [side, Table.get_put _ _ _ _ (v.isLt.trans_le cap) (y.isLt.trans_le cap), atSide]
      by_cases e : y = v
      · subst v; simp
      · have ev : y.val ≠ v.val := fun he => e (Fin.ext he)
        simp only [if_neg ev, Option.some.injEq, if_neg (Ne.symm e)]
        simpa [xs, ex] using cutval

/-- Form the local specification before comparing with dense normalization. -/
def localSystem (decode : α → ℚ) (D : System (Fin n) ℚ) (down up : Fin n → List (Fin n)) :
    Change α n → System (Fin n) ℚ
  | .arc a b => insert D a b (down b) (up a)
  | .above x c => clip D (down x) [] (decode c)
  | .below x c => clip D [] (up x) (decode c)
  | .fix x c => fixAt D x (decode c) (down x) (up x)
  | .unchanged => D

private theorem update_local (lt : α → α → Result Bool) (decode : α → ℚ)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b) (H : ℕ)
    (next prev : Rows n h) (zero one : α) (hz : decode zero = 0) (ho : decode one = 1)
    (w : Walls α h) (D : System (Fin n) ℚ) (rep : aligned decode w D)
    (cap : n ≤ 2^h) (op : Change α n) :
    aligned decode (update lt next prev H zero one w op).value
      (localSystem decode D (visit (fun z : Fin n => (next.get z.val).value) H)
        (visit (fun z : Fin n => (prev.get z.val).value) H) op) := by
  constructor
  all_goals
    intro y
    simp only [update, side_value lt decode hc _ _ _ _ _ _ _ cap y]
    cases op <;>
      simp only [plan, atSide, localSystem, PolylogGraph.insert, clip, fixAt, isolate, rep.1, rep.2, hz, ho,
        Bool.false_eq_true, if_false, if_true, List.not_mem_nil, List.mem_filter,
        decide_eq_true_eq, Option.some.injEq, reduceCtorEq]
    all_goals first | rfl | (split_ifs <;> simp_all)

def permitted (D : System (Fin n) ℚ) (decode : α → ℚ) : Change α n → Prop
  | .fix x c => (D.lower x < decode c ∧ decode c < D.upper x) ∧ D.edge x x = false
  | _ => True

/-- Both resulting stored tables agree literally, label by label, with the
canonical walls obtained by the reference `graphRank` normalization. -/
theorem update_reference (lt : α → α → Result Bool) (decode : α → ℚ)
    (correct : ∀ a b, (lt a b).value = true ↔ decode a < decode b) (H : ℕ)
    (next prev : Rows n h) (zero one : α) (hz : decode zero = 0) (ho : decode one = 1)
    (w : Walls α h) (D : System (Fin n) ℚ) (rep : aligned decode w D) (cap : n ≤ 2^h)
    (hn : ∀ x y : Fin n, y ∈ (next.get x.val).value ↔ D.edge x y = true)
    (hp : ∀ x y : Fin n, y ∈ (prev.get x.val).value ↔ D.edge y x = true)
    (rank : Fin n → ℕ) (hr : ∀ x y, D.edge x y = true → rank x < rank y)
    (height : ∀ x, rank x < H) (norm : Normalized D)
    (op : Change α n) (valid : permitted D decode op)
    (X : Fin n → ℝ) (feasible : (raw decode D op).toReal.StrictlyFeasible X) :
    let data := raw decode D op
    aligned decode (update lt next prev H zero one w op).value
      (OrderRegion.normalize data (rankOrder (GraphOrder.graphRank data))) := by
  have a := update_local lt decode correct H next prev zero one hz ho w D rep cap op
  let down := visit (fun y : Fin n => (next.get y.val).value) H
  let up := visit (fun y : Fin n => (prev.get y.val).value) H
  have hd x y : y ∈ down x ↔ Reaches D x y := descendants_exact D _ hn rank hr H height x y
  have hu x y : y ∈ up x ↔ Reaches D y x := ancestors_exact D _ hp rank hr H height x y
  have eq : localSystem decode D down up op =
      OrderRegion.normalize (raw decode D op) (rankOrder (GraphOrder.graphRank (raw decode D op))) := by
    cases op with
    | arc x y => exact insert_eq_reference D norm x y _ _ (hd y) (hu x) X feasible
    | above x c => exact above_eq_reference D norm x _ (hd x) _ X feasible
    | below x c => exact below_eq_reference D norm x _ (hu x) _ X feasible
    | fix x c => exact fix_eq_reference D norm x _ valid.1 valid.2 _ _ (hd x) (hu x) X feasible
    | unchanged => exact eq_reference D D rfl norm (fun _ => Iff.rfl) X feasible
  change aligned decode _ (localSystem decode D down up op) at a
  rw [eq] at a
  exact a

namespace Address

open PolylogBits

/-- A bit-block address with an erased certificate that it denotes an
endpoint at the common capacity. There is no copy of the endpoint's digits
in the runtime address. -/
abbrev Addr (S : Store) (heap : Heap) (level : ℕ) :=
  { i : ℕ // ∃ a : S.Ref level, Represents S heap i a }

variable {S : Store} {heap : Heap} {level : ℕ}

private noncomputable def block (p : Addr S heap level) : S.Ref level := p.property.choose

private theorem rep (p : Addr S heap level) : Represents S heap p.val (block p) :=
  p.property.choose_spec

/-- Mathematical coordinate, for the common denominator `2^D`. -/
noncomputable def decode (D : ℕ) (p : Addr S heap level) : ℚ :=
  value S level (block p) / (2 : ℚ)^D

def less (a b : Addr S heap level) : Result Bool :=
  let r := heap.lessAddr level a.val b.val
  ⟨r.1, r.2⟩

theorem correct (valid : heap.Valid) (D : ℕ) (a b : Addr S heap level) :
    (less a b).value = true ↔ decode D a < decode D b := by
  rw [less, Heap.lessAddr_refines S valid (rep a) (rep b)]
  simp only [PolylogBits.less_correct, decode, div_lt_div_iff_of_pos_right (by positivity : (0:ℚ) < 2^D)]
  exact_mod_cast Iff.rfl

theorem cost (valid : heap.Valid) (a b : Addr S heap level) : (less a b).work = 3*level+2 := by
  simp only [less, Heap.lessAddr_refines S valid (rep a) (rep b), PolylogBits.less_work]

theorem injective (valid : heap.Valid) (D : ℕ) : Function.Injective (decode (S:=S) (heap:=heap) (level:=level) D) := by
  intro a b eq
  have h : (value S level (block a) : ℚ) = value S level (block b) :=
    (div_left_inj' (by positivity : (2:ℚ)^D ≠ 0)).mp eq
  apply Subtype.ext
  apply ((rep a).same_iff valid (rep b)).mpr
  apply value_injective S level
  exact_mod_cast h

/-- Wall mutation specialized to comparisons on concrete heap addresses.
The comparator cost uses the block-access counter of `Heap.lessAddr`. -/
theorem update_heap_work (valid : heap.Valid) (next prev : Rows n h) (d : ℕ)
    (hn : ∀ y : Fin n, (next.get y.val).value.length ≤ d)
    (hp : ∀ y : Fin n, (prev.get y.val).value.length ≤ d)
    (H : ℕ) (zero one : Addr S heap level) (w : Walls (Addr S heap level) h)
    (op : Change (Addr S heap level) n) :
    (update less next prev H zero one w op).work ≤
      2*((d+1)^H * (13*h+(3*level+2)+12) + 5*h + 6) + 8*h + 9 :=
  update_work _ _ (fun a b => (cost valid a b).le) _ _ _ hn hp _ _ _ _ _

end Address
end SortingAdversary.Continuous.PolylogWallTables
