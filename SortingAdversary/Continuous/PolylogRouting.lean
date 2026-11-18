import SortingAdversary.Continuous.PolylogFreeze
import SortingAdversary.Optimal.PrimitiveWork

/-!
# Persistent ancestor tables and lowest-common-ancestor routing

A node's row maps depth to its ancestor's identifier and incoming anchor.
A child inherits the parent's row with one point update. The binary tables
share every unchanged subtree. Identifiers are indices in the node creation
sequence; this sequence of *full paths* occurs only in the correctness proof.
Queries binary-search the last depth with equal identifiers and read the first
child below it. All costs count word operations and accesses to stored tree
records. Anchors are carried as references, so routing need not inspect their
digits.
-/

namespace SortingAdversary.Continuous.PolylogRouting

open TreeState
open SortingAdversary.Optimal.PrimitiveWork (Result)

/-- Persistent table addressed by the low bits of an index, in order. -/
inductive Table (α : Type) : ℕ → Type
  | leaf : α → Table α 0
  | node : Table α h → Table α h → Table α (h + 1)

namespace Table

def fill (v : α) : (h : ℕ) → Table α h
  | 0 => .leaf v
  | h+1 => let t := fill v h; .node t t

def get : Table α h → ℕ → Result α
  | .leaf x, _ => ⟨x, 1⟩
  | .node l r, i =>
    let a := if i % 2 = 0 then get l (i / 2) else get r (i / 2)
    ⟨a.value, a.work + 4⟩

def put : Table α h → ℕ → α → Result (Table α h)
  | .leaf _, _, x => ⟨.leaf x, 1⟩
  | .node l r, i, x =>
    if i % 2 = 0 then
      let a := put l (i / 2) x
      ⟨.node a.value r, a.work + 5⟩
    else
      let a := put r (i / 2) x
      ⟨.node l a.value, a.work + 5⟩

@[simp] theorem get_work (t : Table α h) (i : ℕ) : (t.get i).work = 4 * h + 1 := by
  induction t generalizing i with
  | leaf => rfl
  | node l r ihl ihr => dsimp only [get]; split <;> simp only [ihl, ihr] <;> omega

@[simp] theorem put_work (t : Table α h) (i : ℕ) (v : α) :
    (t.put i v).work = 5 * h + 1 := by
  induction t generalizing i with
  | leaf => rfl
  | node l r ihl ihr => dsimp only [put]; split <;> simp only [ihl, ihr] <;> omega

@[simp] theorem get_fill (x : α) (h i : ℕ) : ((fill x h).get i).value = x := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp [fill, get, ih]

theorem get_put (t : Table α h) (i j : ℕ) (x : α) (hi : i < 2^h) (hj : j < 2^h) :
    ((t.put i x).value.get j).value = if j = i then x else (t.get j).value := by
  induction t generalizing i j with
  | leaf =>
    have ei : i = 0 := by simpa using hi
    have ej : j = 0 := by simpa using hj
    simp [ei, ej, put, get]
  | @node h l r ihl ihr =>
    rw [pow_succ] at hi hj
    have hi' : i / 2 < 2^h := by omega
    have hj' : j / 2 < 2^h := by omega
    by_cases a : i % 2 = 0 <;> by_cases b : j % 2 = 0
    all_goals
      simp only [put, get, a, b, if_true, if_false, ihl _ _ hi' hj', ihr _ _ hi' hj']
      split_ifs <;> first | rfl | omega

end Table

/-- `anchor` may be a reference into the exact dyadic store. -/
structure Entry (α : Type) where
  id : ℕ
  anchor : α

structure Row (α : Type) (h : ℕ) where
  depth : ℕ
  table : Table (Entry α) h

def root (dummy : α) (h : ℕ) : Row α h := ⟨0, Table.fill ⟨0, dummy⟩ h⟩

def child (p : Row α h) (id : ℕ) (c : α) : Result (Row α h) :=
  let a := p.table.put (p.depth + 1) ⟨id, c⟩
  ⟨⟨p.depth+1, a.value⟩, a.work + 2⟩

@[simp] theorem child_work (p : Row α h) (id : ℕ) (c : α) :
    (child p id c).work = 5 * h + 3 := by simp [child]

/-- A node gets its creation index. Existing rows remain correct when a child
is allocated, even if an arbitrarily old row is subsequently queried. -/
structure Represents [DecidableEq α] (nodes : List (List α)) (p : List α) (r : Row α h) : Prop where
  depth : r.depth = p.length
  fits : p.length < 2^h
  mem : ∀ d ≤ p.length, p.take d ∈ nodes
  ids : ∀ d ≤ p.length, (r.table.get d).value.id = nodes.idxOf (p.take d)
  anchors : ∀ (i : ℕ) (hi : i < p.length), (r.table.get (i+1)).value.anchor = p[i]

theorem root_represents [DecidableEq α] (dummy : α) (h : ℕ) :
    Represents [[]] [] (root dummy h) := by
  constructor
  · rfl
  · exact Nat.two_pow_pos h
  · simp
  · intro d hd; simp [root]
  · simp

theorem Represents.append [DecidableEq α] {nodes : List (List α)} {p : List α} {r : Row α h}
    (v : Represents nodes p r) (more : List (List α)) : Represents (nodes ++ more) p r := by
  refine ⟨v.depth, v.fits, fun i hi => List.mem_append_left _ (v.mem i hi), ?_, v.anchors⟩
  intro i hi
  rw [List.idxOf_append_of_mem (v.mem i hi), v.ids i hi]

theorem child_represents [DecidableEq α] {nodes : List (List α)} {p : List α} {r : Row α h}
    (v : Represents nodes p r) (c : α) (fresh : p ++ [c] ∉ nodes) (space : p.length + 1 < 2^h) :
    Represents (nodes ++ [p ++ [c]]) (p ++ [c]) (child r nodes.length c).value := by
  have len : (p ++ [c]).length = p.length+1 := by simp
  constructor
  · simp [child, v.depth]
  · simpa [len] using space
  · intro d hd
    by_cases old : d ≤ p.length
    · rw [List.take_append_of_le_length old]
      exact List.mem_append_left _ (v.mem d old)
    · have e : d = (p ++ [c]).length := by omega
      simp [e]
  · intro d hd
    simp only [child, v.depth, Table.get_put _ _ _ _ space (by omega : d < 2^h)]
    by_cases old : d ≤ p.length
    · rw [if_neg (by omega), List.take_append_of_le_length old,
        List.idxOf_append_of_mem (v.mem d old), v.ids d old]
    · have e : d = p.length+1 := by omega
      rw [if_pos e, show d = (p ++ [c]).length by omega, List.take_length]
      simp [List.idxOf_append_of_notMem fresh]
  · intro i hi
    simp only [child, v.depth, Table.get_put _ _ _ _ space (by omega : i+1 < 2^h)]
    by_cases old : i < p.length
    · simp [show i ≠ p.length by omega, List.getElem_append_left old, v.anchors i old]
    · have e : i = p.length := by omega
      subst i
      simp

/-- Specification-only longest common prefix depth. -/
def common [DecidableEq α] : List α → List α → ℕ
  | a :: as, b :: bs => if a = b then common as bs + 1 else 0
  | _, _ => 0

private theorem common_bound [DecidableEq α] (p q : List α) : common p q ≤ min p.length q.length := by
  induction p generalizing q with
  | nil => simp [common]
  | cons a as ih =>
    cases q with
    | nil => simp [common]
    | cons b bs =>
      have hh := ih bs
      simp only [common, List.length_cons]
      split <;> omega

private theorem take_eq [DecidableEq α] (p q : List α) (d : ℕ)
    (hd : d ≤ min p.length q.length) : p.take d = q.take d ↔ d ≤ common p q := by
  induction d generalizing p q with
  | zero => simp
  | succ d ih =>
    cases p with
    | nil => simp at hd
    | cons a as =>
      cases q with
      | nil => simp at hd
      | cons b bs =>
        simp only [List.length_cons] at hd
        by_cases h : a = b
        · subst b
          simpa [common] using ih as bs (by omega)
        · simp [common, h]

/-- Bisection on a closed interval, with a fixed number of halvings.
The callback counts its own work. -/
def bisect (test : ℕ → Result Bool) : ℕ → ℕ → ℕ → Result ℕ
  | 0, lo, _ => ⟨lo, 1⟩
  | h+1, lo, hi =>
    let m := (lo + hi + 1) / 2
    let t := test m
    let r := if t.value then bisect test h m hi else bisect test h lo (m-1)
    ⟨r.value, t.work + r.work + 6⟩

private theorem bisect_eq (test : ℕ → Result Bool) (target : ℕ) (h lo hi : ℕ)
    (left : lo ≤ target) (right : target ≤ hi) (w : hi-lo < 2^h)
    (ht : ∀ m, lo ≤ m → m ≤ hi → ((test m).value = true ↔ m ≤ target)) :
    (bisect test h lo hi).value = target := by
  induction h generalizing lo hi with
  | zero => simp only [pow_zero] at w; change lo = target; omega
  | succ h ih =>
    rw [pow_succ] at w
    let m := (lo + hi + 1) / 2
    have hm : lo ≤ m ∧ m ≤ hi := by dsimp [m]; omega
    change (if (test m).value then bisect test h m hi else bisect test h lo (m-1)).value = _
    split
    · rename_i hb
      apply ih m hi ((ht m hm.1 hm.2).mp hb) right (by dsimp [m]; omega)
      exact fun u hu => ht u (hm.1.trans hu)
    · rename_i hb
      have hmt : ¬m ≤ target := mt (ht m hm.1 hm.2).mpr hb
      apply ih lo (m-1) left (by omega) (by dsimp [m]; omega)
      exact fun u hu hhi => ht u hu (by omega)

private theorem bisect_work (test : ℕ → Result Bool) (B : ℕ) (cost : ∀ d, (test d).work ≤ B)
    (h lo hi : ℕ) : (bisect test h lo hi).work ≤ h * (B+6) + 1 := by
  induction h generalizing lo hi with
  | zero => simp [bisect]
  | succ h ih =>
    have ht := cost ((lo+hi+1)/2)
    dsimp only [bisect]
    split
    all_goals
      rw [Nat.succ_mul]
      apply Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add ht (ih _ _)) 6)
      omega

def sameAncestor (u v : Row α h) (d : ℕ) : Result Bool :=
  let a := u.table.get d
  let b := v.table.get d
  ⟨a.value.id == b.value.id, a.work + b.work + 1⟩

def nextAnchor (u : Row α h) (d : ℕ) : Result (Option α) :=
  if d < u.depth then
    let a := u.table.get (d+1)
    ⟨some a.value.anchor, a.work + 3⟩
  else ⟨none, 1⟩

def fromChildren : Option α → Option α → Routing α
  | none, none => .coordinates
  | none, some c => .leftFree c
  | some c, none => .rightFree c
  | some c, some d => .anchors c d

def query (u v : Row α h) : Result (Routing α) :=
  let d := bisect (sameAncestor u v) h 0 (min u.depth v.depth)
  let a := nextAnchor u d.value
  let b := nextAnchor v d.value
  ⟨fromChildren a.value b.value, d.work + a.work + b.work + 3⟩

private theorem nextAnchor_eq [DecidableEq α] {nodes : List (List α)} {p : List α} {u : Row α h}
    (v : Represents nodes p u) (d : ℕ) : (nextAnchor u d).value = p[d]? := by
  by_cases hd : d < p.length
  · simp [nextAnchor, v.depth, hd, v.anchors d hd]
  · simp [nextAnchor, v.depth, hd]

private theorem route_common [LinearOrder α] (p q : List α) :
    fromChildren p[common p q]? q[common p q]? = route p q := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a as ih =>
    cases q with
    | nil => rfl
    | cons b bs =>
      by_cases h : a = b
      · subst b
        simpa [common, route] using ih bs
      · simp [common, route, h, fromChildren]

/-- Computing the node of divergence gives exactly the semantic tree router. -/
theorem query_eq_route [LinearOrder α] {nodes : List (List α)} {p q : List α} {u v : Row α h}
    (hu : Represents nodes p u) (hv : Represents nodes q v) :
    (query u v).value = route p q := by
  have cb := common_bound p q
  have hd : (bisect (sameAncestor u v) h 0 (min u.depth v.depth)).value = common p q := by
    rw [hu.depth, hv.depth]
    apply bisect_eq _ _ _ _ _ (Nat.zero_le _) cb (by have := hu.fits; omega)
    intro i _ hi
    have iu : i ≤ p.length := hi.trans (min_le_left ..)
    have iv : i ≤ q.length := hi.trans (min_le_right ..)
    simp only [sameAncestor, beq_iff_eq, hu.ids i iu, hv.ids i iv]
    exact (List.idxOf_inj (hu.mem i iu)).trans (take_eq p q i hi)
  simp only [query, hd, nextAnchor_eq hu, nextAnchor_eq hv, route_common]

/-- At most a quadratic number of word and record operations in the table
height; a point update takes linear work in the same height. -/
theorem query_work (u v : Row α h) : (query u v).work ≤ h*(8*h+9) + 8*h + 12 := by
  have cs : ∀ d, (sameAncestor u v d).work ≤ 8*h+3 := by
    intro d; simp [sameAncestor]; omega
  have bs := bisect_work _ _ cs h 0 (min u.depth v.depth)
  change _ ≤ h * (8*h + 9) + 1 at bs
  have cn (w : Row α h) (d : ℕ) : (nextAnchor w d).work ≤ 4*h+4 := by
    dsimp only [nextAnchor]; split <;> simp
  let d := (bisect (sameAncestor u v) h 0 (min u.depth v.depth)).value
  have ca := cn u d
  have cb := cn v d
  change _ + (nextAnchor u d).work + (nextAnchor v d).work + 3 ≤ _
  omega

/-- A routing carries references to the two child anchors, if present. -/
def decodeRoute (f : α → β) : Routing α → Routing β
  | .coordinates => .coordinates
  | .leftFree c => .leftFree (f c)
  | .rightFree c => .rightFree (f c)
  | .anchors c d => .anchors (f c) (f d)

theorem route_map [LinearOrder α] (f : α → ℚ) (inj : Function.Injective f)
    (p q : List α) : decodeRoute f (route p q) = route (p.map f) (q.map f) := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a as ih =>
    cases q with
    | nil => rfl
    | cons b bs =>
      by_cases h : a = b
      · subst b; simpa [route] using ih bs
      · simp [route, h, inj.ne h, decodeRoute]

private def pick (b : Bool) : Answer := if b then .less else .greater

/-- Compare references using the supplied counted exact comparison. Predecessor
heights are evaluated only when comparing two free labels with equal walls. -/
def frozenAt (lt : α → α → Result Bool) (wall : Fin n → α) (depth : Fin n → Result ℕ)
    (q : Query n) : Routing α → Result Answer
  | .coordinates =>
    let first := lt (wall q.left) (wall q.right)
    if first.value then ⟨.less, first.work + 4⟩ else
      let second := lt (wall q.right) (wall q.left)
      if second.value then ⟨.greater, first.work + second.work + 5⟩ else
        let l := depth q.left
        let r := depth q.right
        let b := l.value * n + q.left.val < r.value * n + q.right.val
        ⟨if b then .less else .greater, first.work + second.work + l.work + r.work + 12⟩
  | .leftFree c =>
    let a := lt (wall q.left) c
    ⟨pick a.value, a.work + 3⟩
  | .rightFree c =>
    let a := lt (wall q.right) c
    ⟨pick (!a.value), a.work + 4⟩
  | .anchors c d =>
    let a := lt c d
    ⟨pick a.value, a.work + 2⟩

theorem frozenAt_work (lt : α → α → Result Bool) (wall : Fin n → α)
    (depth : Fin n → Result ℕ) (B H : ℕ) (ltCost : ∀ a b, (lt a b).work ≤ B)
    (heightCost : ∀ x, (depth x).work ≤ H) (q : Query n) (r : Routing α) :
    (frozenAt lt wall depth q r).work ≤ 2*B + 2*H + 12 := by
  cases r with
  | coordinates =>
    have l := ltCost (wall q.left) (wall q.right)
    have r := ltCost (wall q.right) (wall q.left)
    have dl := heightCost q.left
    have dr := heightCost q.right
    dsimp only [frozenAt]
    split <;> (try split) <;> dsimp only <;> omega
  | leftFree c => dsimp [frozenAt]; have := ltCost (wall q.left) c; omega
  | rightFree c => dsimp [frozenAt]; have := ltCost (wall q.right) c; omega
  | anchors c d => dsimp [frozenAt]; have := ltCost c d; omega

theorem frozenAt_eq (lt : α → α → Result Bool) (decode : α → ℚ)
    (compare_correct : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    (tree : State n ℚ) (wall : Fin n → α) (walls_correct : ∀ x, decode (wall x) = tree.system.lower x)
    (depth : Fin n → Result ℕ) (q : Query n) (r : Routing α) :
    (frozenAt lt wall depth q r).value =
      PolylogFreeze.answerAt (decodeRoute decode r) tree (fun x => (depth x).value) q := by
  cases r with
  | coordinates =>
    simp only [frozenAt, compare_correct, walls_correct, decodeRoute,
      PolylogFreeze.answerAt, PolylogFreeze.tie]
    split
    · rename_i h; simp [h]
    · rename_i hn
      split
      · rename_i h; simp [hn, h.ne.symm]
      · rename_i hm
        have he := le_antisymm (le_of_not_gt hm) (le_of_not_gt hn)
        simp [he]
  | leftFree c => simp [frozenAt, decodeRoute, PolylogFreeze.answerAt, pick,
      compare_correct, walls_correct]
  | rightFree c => simp [frozenAt, decodeRoute, PolylogFreeze.answerAt, pick,
      Bool.eq_false_iff, compare_correct, walls_correct]
  | anchors c d => simp [frozenAt, decodeRoute, PolylogFreeze.answerAt, pick, compare_correct]

/-- The combined implementation charges two row accesses and obtains the routed
anchors, dyadic comparisons, and both predecessor traversals from their code. -/
def frozenQuery (rows : Fin n → Row α h) (lt : α → α → Result Bool)
    (wall : Fin n → α) (parents : Fin n → List (Fin n)) (H : ℕ) (q : Query n) : Result Answer :=
  let r := query (rows q.left) (rows q.right)
  let a := frozenAt lt wall (PolylogFreeze.height parents H) q r.value
  ⟨a.value, r.work + a.work + 3⟩

theorem frozenQuery_work (rows : Fin n → Row α h) (lt : α → α → Result Bool)
    (wall : Fin n → α) (parents : Fin n → List (Fin n)) (H d B : ℕ)
    (deg : ∀ x, (parents x).length ≤ d) (cost : ∀ a b, (lt a b).work ≤ B) (q : Query n) :
    (frozenQuery rows lt wall parents H q).work ≤
      h*(8*h+9) + 8*h + 2*B + 2*PolylogFreeze.heightBudget d H + 27 := by
  have rq := query_work (rows q.left) (rows q.right)
  have aq := frozenAt_work lt wall _ B _ cost (PolylogFreeze.height_work_le parents d deg H)
    q (query (rows q.left) (rows q.right)).value
  dsimp only [frozenQuery]
  omega

theorem frozenQuery_eq [LinearOrder α] (nodes : List (List α)) (paths : Fin n → List α)
    (rows : Fin n → Row α h) (hr : ∀ x, Represents nodes (paths x) (rows x))
    (lt : α → α → Result Bool) (decode : α → ℚ) (inj : Function.Injective decode)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    (tree : State n ℚ) (hp : ∀ x, (paths x).map decode = tree.location x)
    (wall : Fin n → α) (hw : ∀ x, decode (wall x) = tree.system.lower x)
    (parents : Fin n → List (Fin n)) (H : ℕ) (q : Query n) :
    (frozenQuery rows lt wall parents H q).value =
      PolylogFreeze.answer tree (fun x => (PolylogFreeze.height parents H x).value) q := by
  simp only [frozenQuery, frozenAt_eq lt decode hc tree wall hw, query_eq_route (hr _) (hr _),
    route_map decode inj, hp, PolylogFreeze.answer]

/-- Refinement of the semantic policy that obtains parents by scanning all
labels. The measured query uses the stored lists in whichever order they were
maintained. -/
theorem frozenQuery_eq_scan [LinearOrder α] (nodes : List (List α)) (paths : Fin n → List α)
    (rows : Fin n → Row α h) (hr : ∀ x, Represents nodes (paths x) (rows x))
    (lt : α → α → Result Bool) (decode : α → ℚ) (inj : Function.Injective decode)
    (hc : ∀ a b, (lt a b).value = true ↔ decode a < decode b)
    (tree : State n ℚ) (hp : ∀ x, (paths x).map decode = tree.location x)
    (wall : Fin n → α) (hw : ∀ x, decode (wall x) = tree.system.lower x)
    (parents : Fin n → List (Fin n)) (adj : ∀ x y, x ∈ parents y ↔ tree.system.edge x y = true)
    (H : ℕ) (q : Query n) :
    (frozenQuery rows lt wall parents H q).value =
      PolylogFreeze.answer tree (fun y => (PolylogFreeze.height
        (fun v => (List.finRange n).filter (fun u => tree.system.edge u v)) H y).value) q := by
  rw [frozenQuery_eq nodes paths rows hr lt decode inj hc tree hp wall hw]
  have he := PolylogFreeze.height_ext parents
    (fun v => (List.finRange n).filter (fun u => tree.system.edge u v))
    (fun x y => by simpa using adj y x) H
  rw [show (fun x => (PolylogFreeze.height parents H x).value) = _ from funext he]

end SortingAdversary.Continuous.PolylogRouting
