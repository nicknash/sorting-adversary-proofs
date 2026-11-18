import SortingAdversary.Continuous.PolylogAnchorWrite
import SortingAdversary.Continuous.PolylogHierarchy

/-!
# The four branches of an active comparison

A failed mass test specifies the original label whose interval has to be
split. Only that branch allocates an anchor. The two-anchored branch compares
the stored block addresses and does not prepare a neighborhood.
-/

namespace SortingAdversary.Continuous.PolylogActive

open Controller PolylogBits TreeState
open PolylogRouting (Table Row decodeRoute)
open Optimal.PrimitiveWork (Result)

variable {n h : ℕ}

inductive Decision (n : ℕ)
  | answer (a : Answer)
  | refine (x : Fin n)

def decideTest (x : Fin n) (flip : Bool) (test : Option Answer) : Decision n :=
  match test with
  | none => .refine x
  | some a => .answer (if flip then reverseAnswer a else a)

def branch (heap : Heap) (level : ℕ) (pair : Fin n → Fin n → Result (Option Answer))
    (threshold : Fin n → ℕ → Result (Option Answer)) (q : Query n) : Routing ℕ → Result (Decision n)
  | .coordinates =>
    let t := pair q.left q.right
    ⟨decideTest (min q.left q.right) false t.value, t.work + 3⟩
  | .leftFree c =>
    let t := threshold q.left c
    ⟨decideTest q.left false t.value, t.work + 2⟩
  | .rightFree c =>
    let t := threshold q.right c
    ⟨decideTest q.right true t.value, t.work + 3⟩
  | .anchors a b =>
    let c := heap.lessAddr level a b
    ⟨.answer (if c.1 then .less else .greater), c.2 + 2⟩

theorem lessAddr_work (heap : Heap) (level a b : ℕ) : (heap.lessAddr level a b).2 = 3*level+2 := by
  induction level generalizing a b with
  | zero => rfl
  | succ d ih =>
    simp only [Heap.lessAddr]
    split <;> simp [ih, Nat.mul_succ, Nat.add_assoc]

theorem branch_work (heap : Heap) (level : ℕ) (pair : Fin n → Fin n → Result (Option Answer))
    (threshold : Fin n → ℕ → Result (Option Answer)) (q : Query n) (r : Routing ℕ) (B : ℕ)
    (hp : ∀ x y, (pair x y).work ≤ B) (ht : ∀ x c, (threshold x c).work ≤ B) :
    (branch heap level pair threshold q r).work ≤ max B (3*level+2) + 3 := by
  cases r <;> simp only [branch]
  · exact Nat.add_le_add_right ((hp _ _).trans (le_max_left ..)) _
  · rename_i c
    have hm := le_max_left B (3*level+2)
    have hl := ht q.left c
    omega
  · exact Nat.add_le_add_right ((ht _ _).trans (le_max_left ..)) _
  · rw [lessAddr_work]
    omega

def attempt (loc : Table (PolylogHierarchy.Cursor h) h) (heap : Heap) (level : ℕ)
    (pair : Fin n → Fin n → Result (Option Answer))
    (threshold : Fin n → ℕ → Result (Option Answer)) (q : Query n) : Result (Decision n) :=
  let l := loc.get q.left.val
  let r := loc.get q.right.val
  let route := PolylogRouting.query l.value.row r.value.row
  let out := branch heap level pair threshold q route.value
  ⟨out.value, l.work+r.work+route.work+out.work+3⟩

theorem attempt_work (loc : Table (PolylogHierarchy.Cursor h) h) (heap : Heap) (level : ℕ)
    (pair : Fin n → Fin n → Result (Option Answer)) (threshold : Fin n → ℕ → Result (Option Answer))
    (q : Query n) (B : ℕ) (hp : ∀ x y, (pair x y).work ≤ B) (ht : ∀ x c, (threshold x c).work ≤ B) :
    (attempt loc heap level pair threshold q).work ≤
      h*(8*h+9)+16*h+max B (3*level+2)+20 := by
  let l := (loc.get q.left.val).value.row
  let r := (loc.get q.right.val).value.row
  have route := PolylogRouting.query_work l r
  have b := branch_work heap level pair threshold q (PolylogRouting.query l r).value B hp ht
  simp only [attempt, Table.get_work]
  change _ + (PolylogRouting.query l r).work + (branch heap level pair threshold q (PolylogRouting.query l r).value).work + 3 ≤ _
  omega

def Decision.realize (M : Memory n) : Decision n → LocalSelection.Result n
  | .answer a => .answer a
  | .refine x => .refine x (PolylogOracle.prefixAnchor M x)

private theorem decideTest_value (M : Memory n) (x : Fin n) (t : Option Answer) :
    (decideTest x false t).realize M = PolylogOracle.respond M x t ∧
    (decideTest x true t).realize M = reverseResult (PolylogOracle.respond M x t) := by
  cases t <;> exact ⟨rfl, rfl⟩

/-- Only the anchor references on the route actually taken need to be valid. -/
theorem attempt_value (M : Memory n) (k : ℕ) (loc : Table (PolylogHierarchy.Cursor h) h)
    (heap : Heap) (level : ℕ) (pair : Fin n → Fin n → Result (Option Answer))
    (threshold : Fin n → ℕ → Result (Option Answer)) (q : Query n) (decode : ℕ → ℚ)
    (hp : (pair q.left q.right).value = PolylogOracle.pairTest M k q.left q.right)
    (route := (PolylogRouting.query (loc.get q.left.val).value.row (loc.get q.right.val).value.row).value)
    (hr : decodeRoute decode route = TreeState.route (M.tree.location q.left) (M.tree.location q.right))
    (htl : ∀ c, route = .leftFree c → (threshold q.left c).value = PolylogOracle.thresholdTest M k q.left (decode c))
    (htr : ∀ c, route = .rightFree c → (threshold q.right c).value = PolylogOracle.thresholdTest M k q.right (decode c))
    (hc : ∀ a b, route = .anchors a b → ((heap.lessAddr level a b).1 = true ↔ decode a < decode b))
    (he : route = (PolylogRouting.query (loc.get q.left.val).value.row (loc.get q.right.val).value.row).value := by rfl) :
    (attempt loc heap level pair threshold q).value.realize M = PolylogOracle.attempt M k q := by
  simp only [attempt, PolylogOracle.attempt, ← he, ← hr]
  cases route with
  | coordinates => simp only [branch, decodeRoute, hp, (decideTest_value M _ _).1]
  | leftFree c => simp only [branch, decodeRoute, htl c rfl, (decideTest_value M _ _).1]
  | rightFree c => simp only [branch, decodeRoute, htr c rfl, (decideTest_value M _ _).2]
  | anchors a b => simp [branch, Decision.realize, decodeRoute, hc a b rfl]

/-- Physical output of selection. A refinement contains the newly allocated
heap and the anchor address, with old records preserved. -/
inductive Output (n : ℕ) (heap : Heap)
  | answer (a : Answer)
  | refine (x : Fin n) (out : PolylogAnchorWrite.Written heap)

def persist {S : Store} {heap : Heap} {level cap : ℕ} (D F : ℕ)
    (v : heap.Valid) (cache : Cached S heap cap) (hd : level ≤ cap)
    {a b : Fin n → S.Ref level} (lo : ∀ x, Cell S heap (a x)) (hi : ∀ x, Cell S heap (b x)) :
    Decision n → Output n heap
  | .answer ans => .answer ans
  | .refine x =>
    .refine x (PolylogAnchorWrite.Written.ofWrite
      (PolylogBlockAnchor.fallbackAddr D F v cache hd (lo x) (hi x)))

def Output.Agrees (out : Output n heap) (S : Store) (level D : ℕ) :
    LocalSelection.Result n → Prop :=
  match out with
  | .answer a => fun r => r = .answer a
  | .refine x c => fun r => ∃ q, r = .refine x q ∧ c.Represents S level D q

theorem persist_correct {S : Store} {heap : Heap} {level cap : ℕ} (D F : ℕ)
    (v : heap.Valid) (cache : Cached S heap cap) (hd : level ≤ cap)
    {a b : Fin n → S.Ref level} (lo : ∀ x, Cell S heap (a x)) (hi : ∀ x, Cell S heap (b x))
    (M : Memory n) (hM : Geometric M) (hg : M.OnGrid F) (hD : D < 2^level) (hF : F+2 ≤ D)
    (hl : ∀ x, PolylogBlockAnchor.coord S D (a x) = M.tree.system.lower x)
    (hu : ∀ x, PolylogBlockAnchor.coord S D (b x) = M.tree.system.upper x)
    (t : Decision n) :
    (persist D F v cache hd lo hi t).Agrees S level D (t.realize M) := by
  cases t with
  | answer a => rfl
  | refine x => exact ⟨_, rfl, PolylogAnchorWrite.write_prefix M x D F v cache hd
      (lo x) (hi x) (hl x) (hu x) hM hg hD hF⟩

end SortingAdversary.Continuous.PolylogActive
