import SortingAdversary.Continuous.PolylogWordWork
import SortingAdversary.Continuous.PolylogRecordProof

/-!
# Dictionary charges for sparse mutations

Pass a block comparator with measured record lookups through the existing
wall-clipping and graph-update routines. The same branches and table writes
produce the same stored state. A comparison charges its scalar operations
and the actual balanced-search paths taken by its block lookups.
-/

namespace SortingAdversary.Continuous.PolylogMutationProfile

open PolylogBits PolylogWordWork PolylogCompare
open PolylogRouting (Table)
open PolylogWallTables PolylogMutation
open Optimal.PrimitiveWork (Result)
variable {α β : Type} {n t b : ℕ}

def profileLess (H : Heap) (b i j : ℕ) : Result Bool :=
  let a := PolylogAddressOrder.less H b i j
  ⟨a.value, a.work+((checkedLessTrace H b i j).run H).work⟩

private structure Profile (F : ℕ) (new old : Result α) : Prop where
  value : new.value = old.value
  cost : new.work ≤ F*old.work

private theorem pad {F : ℕ} (hf : 0 < F) (a : ℕ) : a ≤ F*a := Nat.le_mul_of_pos_left _ hf

private theorem less_profile (H : Heap) (v : H.Valid) {T : ℕ} (pos : 0 < T) (fit : H.next < 2^T)
    (b i j : ℕ) : Profile (9*T+1) (profileLess H b i j) (PolylogAddressOrder.less H b i j) := by
  refine ⟨rfl, ?_⟩
  have actual := checkedLess_dictionary H v pos fit b i j
  have h : (3*T+2)*(PolylogAddressOrder.less H b i j).work ≤ (9*T+1)*(PolylogAddressOrder.less H b i j).work :=
    Nat.mul_le_mul_right _ (by omega)
  apply le_trans _ h
  rw [show 3*T+2 = (3*T+1)+1 by omega,Nat.add_mul,one_mul]
  dsimp [profileLess]
  omega

section Generic

variable {F : ℕ} (hf : 0 < F) {new old : α → α → Result Bool}
    (comp : ∀ i j, Profile F (new i j) (old i j))

include hf comp

private theorem clamp_profile (raise : Bool) (c a : α) :
    Profile F (PolylogWalls.clamp new raise c a) (PolylogWalls.clamp old raise c a) := by
  have h : Profile F (if raise then new a c else new c a) (if raise then old a c else old c a) := by
    cases raise <;> apply comp
  exact ⟨by simp only [PolylogWalls.clamp,h.value], by
    dsimp only [PolylogWalls.clamp]
    rw [Nat.mul_add]
    exact Nat.add_le_add h.cost (pad hf _)⟩

omit comp in
private theorem edit_profile (f g : α → Result α) (fg : ∀ x, Profile F (f x) (g x))
    (tab : Table α t) (xs : List (Fin n)) :
    Profile F (PolylogWalls.edit f tab xs) (PolylogWalls.edit g tab xs) := by
  induction xs generalizing tab with
  | nil => exact ⟨rfl,pad hf 1⟩
  | cons x xs ih =>
    let a := (tab.get x.val).value
    have r := fg a
    have tail := ih (tab.put x.val (g a).value).value
    simp only [PolylogWalls.edit]
    change Profile F ⟨(PolylogWalls.edit f (tab.put x.val (f a).value).value xs).value,_⟩ _
    dsimp only [a] at tail r
    constructor
    · dsimp only; rw [r.value]; exact tail.value
    · dsimp only; rw [r.value]; simp only [Nat.mul_add]
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (pad hf _) r.cost) (pad hf _)) tail.cost) (pad hf _)

private def sparse (lt : α → α → Result Bool) (raise : Bool) (rows : Rows n t) (H : ℕ)
    (tab : Table α t) : Cut α n → Result (Table α t)
  | none => ⟨tab,1⟩
  | some (x,c) =>
    let xs := enumerate rows H x ([],0)
    let r := PolylogWalls.edit (PolylogWalls.clamp lt raise c) tab xs.1
    ⟨r.value,xs.2+r.work+2⟩

private theorem sparse_profile (raise : Bool) (rows : Rows n t) (H : ℕ) (tab : Table α t) (cut : Cut α n) :
    Profile F (sparse new raise rows H tab cut) (sparse old raise rows H tab cut) := by
  cases cut with
  | none => exact ⟨rfl,pad hf 1⟩
  | some z =>
    obtain ⟨x,c⟩ := z
    have ed := edit_profile hf _ _ (clamp_profile hf comp raise c) tab (enumerate rows H x ([],0)).1
    refine ⟨ed.value, ?_⟩
    simp only [sparse,Nat.mul_add]
    exact Nat.add_le_add (Nat.add_le_add (pad hf _) ed.cost) (pad hf _)

private theorem side_profile (raise : Bool) (rows : Rows n t) (H : ℕ) (tab : Table α t)
    (cut : Cut α n) (reset : Option (Fin n)) (unit : α) :
    Profile F (side new raise rows H tab cut reset unit) (side old raise rows H tab cut reset unit) := by
  let u := sparse new raise rows H tab cut
  let z := sparse old raise rows H tab cut
  have h : Profile F u z := sparse_profile hf comp raise rows H tab cut
  cases reset with
  | none =>
    change Profile F ⟨u.value,u.work+1⟩ ⟨z.value,z.work+1⟩
    exact ⟨h.value, by simpa only [Nat.mul_add] using Nat.add_le_add h.cost (pad hf 1)⟩
  | some x =>
    change Profile F ⟨(u.value.put x.val unit).value,u.work+(u.value.put x.val unit).work+2⟩
      ⟨(z.value.put x.val unit).value,z.work+(z.value.put x.val unit).work+2⟩
    rw [h.value]
    exact ⟨rfl, by simpa only [Nat.mul_add] using
      Nat.add_le_add (Nat.add_le_add h.cost (pad hf (z.value.put x.val unit).work)) (pad hf 2)⟩

private theorem update_profile (next prev : Rows n t) (H : ℕ) (lo hi : α) (w : Walls α t) (op : Change α n) :
    Profile F (update new next prev H lo hi w op) (update old next prev H lo hi w op) := by
  let p := plan w op
  have lb := side_profile hf comp true next H w.lower p.value.down p.value.reset lo
  have ub := side_profile hf comp false prev H w.upper p.value.up p.value.reset hi
  dsimp only [p] at *
  exact ⟨by simp only [update,lb.value,ub.value], by
    dsimp only [update]; simp only [Nat.mul_add]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (pad hf _) lb.cost) ub.cost) (pad hf 3)⟩

private theorem core_profile (g : PolylogRows.Graph n t) (w : Walls α t) (k h lo hi)
    (op : Change α n) :
    Profile F (updateCore new g w k h lo hi op) (updateCore old g w k h lo hi op) := by
  have walls := update_profile hf comp g.succs g.preds h lo hi w op
  exact ⟨by simp only [updateCore,walls.value], by
    dsimp only [updateCore]; simp only [Nat.mul_add]
    exact Nat.add_le_add (Nat.add_le_add walls.cost (pad hf _)) (pad hf 2)⟩

end Generic

section Mutations

variable {H : Heap} (valid : H.Valid) {T : ℕ} (pos : 0 < T) (fit : H.next < 2^T)

include valid pos fit

private theorem refine_profile (b : ℕ) (s : Sparse n t) (k lo hi : ℕ) (x : Fin n) (c : ℕ) :
    Profile (9*T+1) (refineState (profileLess H b) s k lo hi x c)
      (refineState (PolylogAddressOrder.less H b) s k lo hi x c) := by
  have u := core_profile (Nat.succ_pos (9*T)) (less_profile H valid pos fit b) s.graph s.walls k
    (ArbitraryLabels.pathHeight k) lo hi (.fix x c)
  exact ⟨by simp only [refineState,u.value], by
    dsimp only [refineState]; simp only [Nat.mul_add]
    exact Nat.add_le_add (Nat.add_le_add u.cost (pad (Nat.succ_pos _) _)) (pad (Nat.succ_pos _) 2)⟩

private theorem record_profile (b : ℕ) (s : Sparse n t) (k lo hi : ℕ) (q : Query n) (a : Answer) :
    Profile (9*T+1) (recordState (profileLess H b) s k lo hi q a)
      (recordState (PolylogAddressOrder.less H b) s k lo hi q a) := by
  let r := PolylogStorage.route s q
  have u := core_profile (Nat.succ_pos (9*T)) (less_profile H valid pos fit b) s.graph s.walls k
    (ArbitraryLabels.pathHeight k) lo hi (forRecord r.value q a)
  dsimp only [r] at u
  exact ⟨by simp only [recordState,u.value], by
    dsimp only [recordState]; simp only [Nat.mul_add]
    exact Nat.add_le_add (Nat.add_le_add (pad (Nat.succ_pos _) _) u.cost) (pad (Nat.succ_pos _) 2)⟩

end Mutations

def refine (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m) : Result (Memory n t b) :=
  let u := m.withHeap w.out.heap w.out.valid w.out.growth
  let r := refineState (profileLess u.heap b) u.spatial k u.zero u.one x w.out.addr
  ⟨{u with spatial := r.value},r.work+2⟩

def record (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer) :
    Result (Memory n t b × Option (Fin n × Fin n)) :=
  let r := PolylogStorage.route m.spatial q
  let z := recordState (profileLess m.heap b) m.spatial k m.zero m.one q a
  ⟨(⟨z.value,m.heap,m.valid,m.typed,m.cache,m.zero,m.one⟩,newArc q a r.value),r.work+z.work+2⟩

def refineCost (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m) := (refine k m x w).work
def recordCost (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer) := (record k m q a).work

theorem refine_value (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m) :
    (refine k m x w).value = (move k m x w).value := by
  let u := m.withHeap w.out.heap w.out.valid w.out.growth
  have r := refine_profile u.valid (Nat.succ_pos u.heap.next.size)
    ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))) b u.spatial k u.zero u.one x w.out.addr
  simp only [refine,move,Memory.less]
  exact congrArg (fun s => {u with spatial := s}) r.value

theorem record_value (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer) :
    (record k m q a).value = (PolylogCompare.record k m q a).value := by
  have r := record_profile m.valid (Nat.succ_pos m.heap.next.size)
    ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))) b m.spatial k m.zero m.one q a
  simp only [record,PolylogCompare.record,Memory.less,r.value]

theorem refineCost_le (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m)
    {T : ℕ} (pos : 0 < T) (fit : w.out.heap.next < 2^T) :
    refineCost k m x w ≤ (9*T+1)*(move k m x w).work := by
  let u := m.withHeap w.out.heap w.out.valid w.out.growth
  have h := refine_profile w.out.valid pos fit b u.spatial k u.zero u.one x w.out.addr
  change _ ≤ (9*T+1)*(w.work + (refineState u.less u.spatial k u.zero u.one x w.out.addr).work + 2)
  calc
    _ ≤ (9*T+1)*((refineState u.less u.spatial k u.zero u.one x w.out.addr).work + 2) := by
      change (refineState (profileLess w.out.heap b) u.spatial k u.zero u.one x w.out.addr).work + 2 ≤ _
      rw [Nat.mul_add]
      exact Nat.add_le_add h.cost (pad (Nat.succ_pos (9*T)) 2)
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

theorem recordCost_le (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer)
    {T : ℕ} (pos : 0 < T) (fit : m.heap.next < 2^T) :
    recordCost k m q a ≤ (9*T+1)*(PolylogCompare.record k m q a).work := by
  have h := record_profile m.valid pos fit b m.spatial k m.zero m.one q a
  dsimp [recordCost,record,PolylogCompare.record,Memory.less]
  simp only [Nat.mul_add]
  exact Nat.add_le_add (Nat.add_le_add (pad (Nat.succ_pos _) _) h.cost) (pad (Nat.succ_pos _) 2)

end SortingAdversary.Continuous.PolylogMutationProfile
