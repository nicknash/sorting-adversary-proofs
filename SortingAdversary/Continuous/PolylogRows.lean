import SortingAdversary.Continuous.PolylogWalls
import SortingAdversary.Continuous.GraphPaths
import SortingAdversary.Optimal.SparseRepairGraph

/-!
# Maintaining the two incidence lists of each free label

Rows are kept in increasing original-label order, as required by the repair
search. Insertion edits two rows. Fixing a coordinate erases its two rows
and removes it from the opposite rows of its old neighbors.
-/

namespace SortingAdversary.Continuous.PolylogRows

open PolylogRouting (Table)
open Optimal.PrimitiveWork (Result)
open Optimal.SparseRepairGraph (eraseVertex addRow addRow_true)

variable {n h : ℕ}

def insertLabel (x : Fin n) : List (Fin n) → Result (List (Fin n))
  | [] => ⟨[x], 2⟩
  | y :: ys =>
    if x < y then ⟨x :: y :: ys, 3⟩
    else if x = y then ⟨y :: ys, 3⟩
    else
      let r := insertLabel x ys
      ⟨y :: r.value, r.work + 4⟩

theorem insertLabel_work (x : Fin n) (ys : List (Fin n)) :
    (insertLabel x ys).work ≤ 4*ys.length+2 := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [insertLabel, List.length_cons]; split_ifs <;> dsimp only <;> omega

theorem insertLabel_mem (x y : Fin n) (ys : List (Fin n)) :
    y ∈ (insertLabel x ys).value ↔ y = x ∨ y ∈ ys := by
  induction ys with
  | nil => simp [insertLabel]
  | cons z zs ih =>
    simp only [insertLabel]
    split_ifs with hlt he
    · simp
    · simp [he]
    · simp only [List.mem_cons, ih]; tauto

theorem insertLabel_sorted (x : Fin n) (ys : List (Fin n)) (hs : ys.Pairwise (· < ·)) :
    (insertLabel x ys).value.Pairwise (· < ·) := by
  induction ys with
  | nil => simp [insertLabel]
  | cons y ys ih =>
    obtain ⟨hy, ht⟩ := List.pairwise_cons.mp hs
    simp only [insertLabel]
    split_ifs with hlt he
    · exact List.pairwise_cons.mpr ⟨fun z hz => (List.mem_cons.mp hz).elim
        (fun h => h ▸ hlt) (fun h => hlt.trans (hy _ h)), hs⟩
    · exact hs
    · exact List.pairwise_cons.mpr ⟨fun z hz => (insertLabel_mem _ _ _ |>.mp hz).elim
        (fun h => h ▸ lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)) (hy _), ih ht⟩

/-- The degree cap bounds the number of inspected cells even on malformed
rows. On a row within that cap this is ordinary deletion. -/
def deleteLabel (x : Fin n) : ℕ → List (Fin n) → Result (List (Fin n))
  | 0, _ | _+1, [] => ⟨[], 1⟩
  | d+1, y::ys =>
    let r := deleteLabel x d ys
    ⟨if y = x then r.value else y :: r.value, r.work + 3⟩

theorem deleteLabel_value (x : Fin n) (d : ℕ) (ys : List (Fin n)) :
    (deleteLabel x d ys).value = (ys.take d).filter (· != x) := by
  induction d generalizing ys with
  | zero => simp [deleteLabel]
  | succ d ih => cases ys with
    | nil => simp [deleteLabel]
    | cons y ys => by_cases h : y = x <;> simp [deleteLabel, ih, h]

theorem deleteLabel_work (x : Fin n) (d : ℕ) (ys : List (Fin n)) :
    (deleteLabel x d ys).work ≤ 3*d+1 := by
  induction d generalizing ys with
  | zero => rfl
  | succ d ih => cases ys with
    | nil => simp [deleteLabel]
    | cons y ys => have := ih ys; simp only [deleteLabel]; omega

private theorem prune_idem (x : Fin n) (d : ℕ) (ys : List (Fin n)) :
    let zs := (ys.take d).filter (· != x)
    (zs.take d).filter (· != x) = zs := by
  dsimp only
  rw [List.take_of_length_le (List.length_filter_le .. |>.trans (List.length_take_le ..))]
  simp [List.filter_filter]

abbrev Rows (n h : ℕ) := Table (List (Fin n)) h

structure Graph (n h : ℕ) where
  succs : Rows n h
  preds : Rows n h

def Graph.Valid (g : Graph n h) (E : Fin n → Fin n → Bool) : Prop :=
  (∀ x : Fin n, (g.succs.get x.val).value = GraphPaths.outgoing E x) ∧
  (∀ x : Fin n, (g.preds.get x.val).value = GraphPaths.outgoing (fun a b => E b a) x)

def empty (n h : ℕ) : Graph n h := ⟨Table.fill [] h, Table.fill [] h⟩

theorem empty_valid (n h : ℕ) : (empty n h).Valid (fun _ _ => false) := by
  constructor <;> intro x <;> simp [empty, GraphPaths.outgoing]

def addToRow (t : Rows n h) (atLabel newLabel : Fin n) : Result (Rows n h) :=
  let old := t.get atLabel.val
  let r := insertLabel newLabel old.value
  let w := t.put atLabel.val r.value
  ⟨w.value, old.work+r.work+w.work+2⟩

theorem addToRow_work (t : Rows n h) (a b : Fin n) :
    (addToRow t a b).work ≤ 9*h+4*(t.get a.val).value.length+6 := by
  have := insertLabel_work b (t.get a.val).value
  simp only [addToRow, Table.put_work, Table.get_work]; omega

private theorem addToRow_value (t : Rows n h) (cap : n ≤ 2^h)
    (E : Fin n → Fin n → Bool) (spec : ∀ x : Fin n, (t.get x.val).value = GraphPaths.outgoing E x)
    (a b x : Fin n) :
    ((addToRow t a b).value.get x.val).value = GraphPaths.outgoing (addRow E a b) x := by
  simp only [addToRow, Table.get_put _ _ _ _ (a.isLt.trans_le cap) (x.isLt.trans_le cap), spec]
  have sorted (F : Fin n → Fin n → Bool) (i : Fin n) :
      (GraphPaths.outgoing F i).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange n).filter _
  by_cases he : x = a
  · subst x
    simp only
    apply (insertLabel_sorted b _ (sorted E a)).eq_of_mem_iff (sorted _ _)
    intro y
    rw [insertLabel_mem, GraphPaths.mem_outgoing, GraphPaths.mem_outgoing, addRow_true]
    tauto
  · rw [if_neg (show x.val ≠ a.val from fun hv => he (Fin.ext hv))]
    apply (sorted E x).eq_of_mem_iff (sorted _ _)
    simp [GraphPaths.mem_outgoing, addRow_true, he]

def add (g : Graph n h) (a b : Fin n) : Result (Graph n h) :=
  let s := addToRow g.succs a b
  let p := addToRow g.preds b a
  ⟨⟨s.value,p.value⟩, s.work+p.work+1⟩

theorem add_valid {g : Graph n h} {E : Fin n → Fin n → Bool} (hg : g.Valid E)
    (cap : n ≤ 2^h) (a b : Fin n) : (add g a b).value.Valid (addRow E a b) := by
  refine ⟨addToRow_value _ cap E hg.1 a b, ?_⟩
  intro x
  have ht : addRow (fun u v => E v u) b a = fun u v => addRow E a b v u := by
    funext u v
    simp [addRow, and_comm]
  simpa only [add, ht] using addToRow_value _ cap _ hg.2 b a x

theorem add_work (g : Graph n h) (a b : Fin n) (d : ℕ)
    (hs : (g.succs.get a.val).value.length ≤ d) (hp : (g.preds.get b.val).value.length ≤ d) :
    (add g a b).work ≤ 18*h + 8*d + 13 := by
  have := addToRow_work g.succs a b
  have := addToRow_work g.preds b a
  simp only [add]; omega

def eraseFrom (d : ℕ) (t : Rows n h) (x : Fin n) (affected : List (Fin n)) : Result (Rows n h) :=
  let ed := PolylogWalls.edit (deleteLabel x d) t affected
  let w := ed.value.put x.val []
  ⟨w.value, ed.work+w.work+1⟩

theorem eraseFrom_work (d : ℕ) (t : Rows n h) (x : Fin n) (affected : List (Fin n)) :
    (eraseFrom d t x affected).work ≤ affected.length*(9*h+3*d+6)+5*h+3 := by
  have hw := PolylogWalls.edit_work _ _ (deleteLabel_work x d) t affected
  rw [show 9*h+(3*d+1)+5 = 9*h+3*d+6 by omega] at hw
  simp only [eraseFrom, Table.put_work]; omega

private theorem eraseFrom_value (d : ℕ) (t : Rows n h) (cap : n ≤ 2^h)
    (E : Fin n → Fin n → Bool) (spec : ∀ x : Fin n, (t.get x.val).value = GraphPaths.outgoing E x)
    (hd : ∀ y : Fin n, (t.get y.val).value.length ≤ d)
    (x : Fin n) (affected : List (Fin n)) (ha : ∀ z, z ∈ affected ↔ E z x = true) (y : Fin n) :
    ((eraseFrom d t x affected).value.get y.val).value = GraphPaths.outgoing (eraseVertex E x) y := by
  simp only [eraseFrom, Table.get_put _ _ _ _ (x.isLt.trans_le cap) (y.isLt.trans_le cap)]
  by_cases he : y = x
  · subst y
    simp [GraphPaths.outgoing, eraseVertex]
  · rw [if_neg (show y.val ≠ x.val from fun hv => he (Fin.ext hv))]
    have hv := PolylogWalls.edit_value (deleteLabel x d) id
      (fun zs => (zs.take d).filter (· != x)) (deleteLabel_value x d) (prune_idem x d)
      cap t affected y
    dsimp only [id_eq] at hv
    rw [List.take_of_length_le (hd y), spec] at hv
    rw [hv]
    by_cases hy : y ∈ affected
    · simp only [if_pos hy, GraphPaths.outgoing, List.filter_filter]
      apply List.filter_congr
      intro z _
      by_cases hz : z = x <;> simp [eraseVertex, he, hz]
    · rw [if_neg hy]
      apply List.filter_congr
      intro z _
      have hx : E y x = false := Bool.eq_false_iff.mpr (fun hh => hy ((ha y).mpr hh))
      by_cases hz : z = x <;> simp [eraseVertex, he, hz, hx]

def erase (g : Graph n h) (d : ℕ) (x : Fin n) : Result (Graph n h) :=
  let o := g.succs.get x.val
  let i := g.preds.get x.val
  let s := eraseFrom d g.succs x i.value
  let p := eraseFrom d g.preds x o.value
  ⟨⟨s.value,p.value⟩, o.work+i.work+s.work+p.work+2⟩

theorem erase_valid {g : Graph n h} {E : Fin n → Fin n → Bool} (hg : g.Valid E)
    (cap : n ≤ 2^h) (d : ℕ)
    (hs : ∀ y : Fin n, (g.succs.get y.val).value.length ≤ d)
    (hp : ∀ y : Fin n, (g.preds.get y.val).value.length ≤ d) (x : Fin n) :
    (erase g d x).value.Valid (eraseVertex E x) := by
  have tr : eraseVertex (fun u v => E v u) x = fun u v => eraseVertex E x v u := by
    funext u v; simp [eraseVertex, and_comm, or_comm]
  constructor
  · apply eraseFrom_value _ _ cap _ hg.1 hs
    intro z; rw [hg.2, GraphPaths.mem_outgoing]
  · intro y
    simpa only [erase, tr] using eraseFrom_value d _ cap _ hg.2 hp x _ (fun z => by
      rw [hg.1, GraphPaths.mem_outgoing]) y

theorem erase_work (g : Graph n h) (d : ℕ) (x : Fin n)
    (hs : (g.succs.get x.val).value.length ≤ d) (hp : (g.preds.get x.val).value.length ≤ d) :
    (erase g d x).work ≤ 2*d*(9*h+3*d+6)+18*h+10 := by
  have h1 := eraseFrom_work d g.succs x (g.preds.get x.val).value
  have h2 := eraseFrom_work d g.preds x (g.succs.get x.val).value
  have hm1 := Nat.mul_le_mul_right (9*h+3*d+6) hp
  have hm2 := Nat.mul_le_mul_right (9*h+3*d+6) hs
  simp only [erase, Table.get_work, two_mul, Nat.add_mul]; omega

end SortingAdversary.Continuous.PolylogRows
