import SortingAdversary.Continuous.PolylogMemory
import SortingAdversary.Continuous.PolylogAdversary
import SortingAdversary.Continuous.PolylogMutation
import SortingAdversary.Continuous.PolylogDictionary

/-!
# Frozen queries on the physical memory

The read-only continuation uses bounded-height predecessor searches, indexed
routing, and the exact address comparator. The counter below charges the
actual search depth in the balanced record dictionary at *every* tag read or
block split. A frozen comparison allocates no dictionary or hierarchy nodes.
-/

namespace SortingAdversary.Continuous.PolylogFrozenQuery

open Optimal.PrimitiveWork (Result)
open PolylogBits (Heap Key)
open PolylogCompare (Memory)
open PolylogRouting (Table)
variable {n t b : ℕ}

private def lookup (H : Heap) (i : ℕ) : Result (Option Key) :=
  let r := PolylogDictionary.lookup i H.record.inner.inner
  ⟨r.1, 4*r.2+2⟩

private theorem lookup_value (H : Heap) (i : ℕ) : (lookup H i).value = H.record[i]? :=
  (PolylogDictionary.lookup_map H.record i).1

/-- Allow four word operations per balanced-tree node examined and two at
the entry/exit. Each key in this dictionary is a single integer address. -/
def lookupBudget (H : Heap) := 12*(H.next.log2+1)+2

private theorem lookup_work (H : Heap) (valid : H.Valid) (i : ℕ) : (lookup H i).work ≤ lookupBudget H := by
  have h := (PolylogDictionary.lookup_map H.record i).2
  have hm : H.record.size.log2 ≤ H.next.log2 := by
    by_cases hz : H.record.size = 0
    · simp [hz]
    · apply (Nat.le_log2 (by have := valid.reserved; omega)).mpr
      exact (Nat.log2_self_le hz).trans valid.record_size
  dsimp only [lookup,lookupBudget]; omega

private def rootTag (H : Heap) (h i : ℕ) : Result Bool :=
  if h = 0 then ⟨decide (i < 2),2⟩ else
    let r := lookup H i
    ⟨r.value.any (fun k => k.1 == h),r.work+3⟩

private theorem rootTag_value (H : Heap) (h i : ℕ) :
    (rootTag H h i).value = PolylogAddressOrder.isRoot H h i := by
  cases h <;> simp [rootTag, lookup_value, PolylogAddressOrder.isRoot]

private theorem rootTag_work (H : Heap) (v : H.Valid) (h i : ℕ) :
    (rootTag H h i).work ≤ lookupBudget H+3 := by
  cases h <;> simp [rootTag, lookup_work H v]

private def compareRoots (H : Heap) : ℕ → ℕ → ℕ → Result Bool
  | 0, i, j => ⟨decide (i < j),2⟩
  | h+1, i, j =>
    let x := lookup H i
    let y := lookup H j
    let p := (x.value.getD (0,0,0)).2
    let q := (y.value.getD (0,0,0)).2
    let r := if p.1 = q.1 then compareRoots H h p.2 q.2 else compareRoots H h p.1 q.1
    ⟨r.value,x.work+y.work+r.work+5⟩

private theorem compareRoots_value (H : Heap) (h i j : ℕ) :
    (compareRoots H h i j).value = (H.lessAddr h i j).1 := by
  induction h generalizing i j with
  | zero => rfl
  | succ h ih =>
    simp only [compareRoots,Heap.lessAddr,Heap.children,lookup_value]
    split <;> rename_i htest <;> simp [ih,htest]

private theorem compareRoots_work (H : Heap) (v : H.Valid) (h i j : ℕ) :
    (compareRoots H h i j).work ≤ h*(2*lookupBudget H+5)+2 := by
  induction h generalizing i j with
  | zero => simp [compareRoots]
  | succ h ih =>
    have hi := lookup_work H v i
    have hj := lookup_work H v j
    simp only [compareRoots,Nat.add_mul,one_mul]
    split <;> apply Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hi hj) (ih _ _)) 5) <;> omega

def less (H : Heap) (h i j : ℕ) : Result Bool :=
  let p := rootTag H h i
  let q := rootTag H h j
  if p.value then
    if q.value then
      let r := compareRoots H h i j
      ⟨r.value,p.work+q.work+r.work+3⟩
    else ⟨false,p.work+q.work+2⟩
  else ⟨if q.value then true else decide (j < i),p.work+q.work+3⟩

theorem less_value (H : Heap) (h i j : ℕ) :
    (less H h i j).value = (PolylogAddressOrder.less H h i j).value := by
  unfold less PolylogAddressOrder.less
  simp only [rootTag_value]
  split <;> (try split) <;> simp only [compareRoots_value]

def compareBudget (H : Heap) (h : ℕ) := (h+1)*(2*lookupBudget H+5)+6

theorem less_work (H : Heap) (v : H.Valid) (h i j : ℕ) :
    (less H h i j).work ≤ compareBudget H h := by
  have p := rootTag_work H v h i
  have q := rootTag_work H v h j
  have r := compareRoots_work H v h i j
  dsimp only [less, compareBudget]
  rw [Nat.add_mul,one_mul]
  split <;> (try split) <;> dsimp only <;> omega

/-- Read two lower walls once. Each evaluation of this two-label callback
inspects at most one label equality; `frozenAt` uses at most four of them. -/
private def wallPair (q : Query n) (l r : ℕ) (x : Fin n) : ℕ :=
  if x = q.left then l else r

private theorem frozenAt_pair (cmp : ℕ → ℕ → Result Bool) (w : Fin n → ℕ) (q : Query n)
    (dep : Fin n → Result ℕ) (r : TreeState.Routing ℕ) :
    PolylogRouting.frozenAt cmp (wallPair q (w q.left) (w q.right)) dep q r =
      PolylogRouting.frozenAt cmp w dep q r := by
  cases r <;> simp [PolylogRouting.frozenAt,wallPair,Ne.symm q.distinct]

/-- The caller stores the stage height `H` at initialization. -/
def query (m : Memory n t b) (H : ℕ) (q : Query n) : Result Answer :=
  let r := PolylogStorage.route m.spatial q
  let l := m.spatial.walls.lower.get q.left.val
  let u := m.spatial.walls.lower.get q.right.val
  let a := PolylogRouting.frozenAt (less m.heap b) (wallPair q l.value u.value)
    (PolylogFreeze.heightFrom (fun x : Fin n => m.spatial.graph.preds.get x.val) H)
    q r.value
  ⟨a.value,r.work+l.work+u.work+a.work+8⟩

theorem query_eq {m : Memory n t b} {D : ℕ} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hm : m.Represents D nodes M) (k : ℕ) (q : Query n) :
    (query m (2^k) q).value = (PolylogAdversary.policy n).frozenAnswer k M q := by
  let w (x : Fin n) := (m.spatial.walls.lower.get x.val).value
  let row (x : Fin n) := m.spatial.graph.preds.get x.val
  let dep := PolylogFreeze.heightFrom row (2^k)
  have costCmp (i j : ℕ) : (less m.heap b i j).value = true ↔ m.decode D i < m.decode D j := by
    rw [less_value]; exact m.less_correct _ _ _
  change (PolylogRouting.frozenAt _ (wallPair q (w q.left) (w q.right)) dep q _).value = _
  rw [frozenAt_pair,PolylogRouting.frozenAt_eq _ _ costCmp M.tree w hm.spatial.walls.1,
    PolylogStorage.route_value hm.spatial (m.decode_injective D)]
  have er (x : Fin n) : (row x).value =
      (PolylogAdversary.policy n).parents M x := hm.spatial.graph.2 x
  have dv (x : Fin n) : (dep x).value =
      (PolylogFreeze.height ((PolylogAdversary.policy n).parents M) (2^k) x).value := by
    rw [show (dep x).value = _ from PolylogFreeze.heightFrom_value row (2^k) x, funext er]
  rw [show (fun x => (dep x).value) = _ from funext dv]
  rfl

def queryBudget (t b d H : ℕ) (heap : Heap) :=
  t*(8*t+9)+24*t+2*compareBudget heap b+2*(PolylogFreeze.heightBudget d H*(4*t+2))+38

theorem query_work (m : Memory n t b) (H d : ℕ) (q : Query n)
    (deg : ∀ x : Fin n, (m.spatial.graph.preds.get x.val).value.length ≤ d) :
    (query m H q).work ≤ queryBudget t b d H m.heap := by
  have r := PolylogStorage.route_work m.spatial q
  have p := PolylogFreeze.heightFrom_work
    (fun x : Fin n => m.spatial.graph.preds.get x.val) d (4*t+1) deg
    (fun x => (Table.get_work _ _).le) H
  let w := wallPair q (m.spatial.walls.lower.get q.left.val).value (m.spatial.walls.lower.get q.right.val).value
  have a := PolylogRouting.frozenAt_work (less m.heap b) w _ (compareBudget m.heap b) _
    (less_work _ m.valid b) p q (PolylogStorage.route m.spatial q).value
  simp only [query,queryBudget,Table.get_work]
  dsimp only [w] at a
  rw [show 4*t+1+1 = 4*t+2 by omega] at a
  omega

private theorem heightBudget_bound (d H : ℕ) : PolylogFreeze.heightBudget d H ≤ (8*(d+1))^(H+1) := by
  induction H with
  | zero => simp [PolylogFreeze.heightBudget]; omega
  | succ H ih =>
    let p := (8*(d+1))^(H+1)
    have hp : 1 ≤ p := Nat.one_le_pow _ _ (by omega)
    have hm : d*(PolylogFreeze.heightBudget d H+4) ≤ d*(p+4) := Nat.mul_le_mul_left _ (by omega)
    change d*(PolylogFreeze.heightBudget d H+4)+2 ≤ _
    rw [pow_succ]
    change _ ≤ p*(8*(d+1))
    nlinarith [Nat.mul_le_mul_left d hp]

theorem admitted_height_work {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n) :
    PolylogFreeze.heightBudget (PolylogAdversary.parameter n) (2^PolylogAdversary.parameter n) ≤
      Optimal.Parameters.logCap n := by
  let k := PolylogAdversary.parameter n
  let R := ArbitraryLabels.pathHeight k
  let u := (k+1)^R
  let p := (8*(k+1))^(R+1)
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by omega)
  have hR : 2^k ≤ R := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
  have hp : p ≤ u * (p+4*u+3) := by
    have := Nat.mul_le_mul_right (p+4*u+3) hu
    omega
  have hs := (PolylogSchedule.admitted_costs hk).2
  change PolylogRepair.repairBound k R ≤ Optimal.Parameters.logCap n at hs
  apply (heightBudget_bound k _).trans
  apply (Nat.pow_le_pow_right (by omega : 0 < 8*(k+1)) (Nat.add_le_add_right hR 1)).trans
  apply le_trans _ hs
  change p ≤ _
  unfold PolylogRepair.repairBound
  change p ≤ 3*u+(u*(p+4*u+3)+1)+(u*u*(5*(R+1)+4)+1)+(6*k+14)
  omega

/-- In the active stage the height-search factor is absorbed by the admitted
recipe. If the two table heights and the address bit width are each bounded
by `L`, frozen work is quadratic in `L+1`. -/
theorem uniform_work {m : Memory n t b} {D : ℕ} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hm : m.Represents D nodes M) (hk : 64 ≤ PolylogAdversary.parameter n)
    (ready : Controller.Ready (PolylogAdversary.parameter n) M) (L : ℕ)
    (ltable : t ≤ L) (lblock : b ≤ L) (lheap : m.heap.next.log2 ≤ L)
    (lcap : Optimal.Parameters.logCap n ≤ L) (q : Query n) :
    (query m (2^PolylogAdversary.parameter n) q).work ≤ 180*(L+1)^2 := by
  let k := PolylogAdversary.parameter n
  have bounds := PolylogMutation.bounded_of_degree hm.spatial.graph k ready.noLoop ready.admissible.degree
  apply (query_work m _ k q bounds.2).trans
  have hs := (admitted_height_work hk).trans lcap
  have t1 : t*(8*t+9) ≤ L*(8*L+9) := by gcongr
  have t2 : 2*(PolylogFreeze.heightBudget k (2^k)*(4*t+2)) ≤ 2*(L*(4*L+2)) := by gcongr
  have t3 : (b+1)*(2*lookupBudget m.heap+5) ≤ (L+1)*(2*(12*(L+1)+2)+5) := by
    unfold lookupBudget; gcongr
  dsimp only [queryBudget,compareBudget]
  change PolylogFreeze.heightBudget k (2^k) ≤ L at hs
  nlinarith

/-- The address envelope for the chosen table height yields a bound in
`n` alone, including every balanced-dictionary lookup in a frozen query. -/
theorem scheduled_work {m : Memory n t b} {D : ℕ} {nodes : List (List ℕ)} {M : Controller.Memory n}
    (hm : m.Represents D nodes M) (hk : 64 ≤ PolylogAdversary.parameter n)
    (ready : Controller.Ready (PolylogAdversary.parameter n) M)
    (table : t ≤ 13+6*(Optimal.Parameters.logCap n+1))
    (block : b ≤ 5+3*(Optimal.Parameters.logCap n+1))
    (heap : m.heap.next < 2^t) (q : Query n) :
    (query m (2^PolylogAdversary.parameter n) q).work ≤
      72000*(Optimal.Parameters.logCap n+1)^2 := by
  let L := Optimal.Parameters.logCap n + 1
  have hL : 1 ≤ L := Nat.succ_pos _
  have ht : t ≤ 19*L := by dsimp [L]; omega
  have hb : b ≤ 19*L := by dsimp [L]; omega
  have hg : m.heap.next.log2 ≤ t := by
    by_contra! ht'
    have nz : m.heap.next ≠ 0 := by have := m.valid.reserved; omega
    have hp := (Nat.pow_le_pow_right (show 0 < 2 by decide) ht'.le).trans (Nat.log2_self_le nz)
    omega
  apply (uniform_work hm hk ready (19*L) ht hb (hg.trans ht) (by dsimp [L]; omega) q).trans
  have e : 19*L+1 ≤ 20*L := by omega
  have p := Nat.mul_le_mul_left 180 (Nat.pow_le_pow_left e 2)
  calc
    180*(19*L+1)^2 ≤ 180*(20*L)^2 := p
    _ = 72000*L^2 := by ring

end SortingAdversary.Continuous.PolylogFrozenQuery
