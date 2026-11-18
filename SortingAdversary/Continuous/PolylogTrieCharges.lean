import SortingAdversary.Continuous.PolylogTrieAllocation
import SortingAdversary.Continuous.PolylogSpace

/-!
# Cumulative persistent-trie allocations

Count the path-copying writes and incidence-list constructors used by the stored controller. A trie of
height t allocates t+1 cells on a write, as witnessed by the address arena
in `PolylogTrieAllocation.replace_spec`. The counts below follow the same
enumerations and repair branches as the executable operations. Ephemeral
superseded trie versions are included.
-/

namespace SortingAdversary.Continuous.PolylogTrieCharges

open PolylogRouting (Table)
open PolylogWallTables PolylogRows PolylogStorage PolylogMutation PolylogCompare
open Optimal.PrimitiveWork (Result)
variable {α : Type} {n t b : ℕ}

private theorem edit_cells (f : α → Result α) (tab : Table α t) (xs : List (Fin n)) :
    xs.length*(t+1) ≤ (PolylogWalls.edit f tab xs).work := by
  induction xs generalizing tab with
  | nil => simp
  | cons x xs ih =>
    have h := ih (tab.put x.val (f (tab.get x.val).value).value).value
    simp only [PolylogWalls.edit,Table.put_work,Table.get_work,List.length_cons,Nat.succ_mul]
    omega

/-- A side update visits each listed occurrence and optionally resets one cell. -/
def sideCells (rows : PolylogRows.Rows n t) (H : ℕ) (cut : Cut α n) (reset : Option (Fin n)) :=
  (match cut with
    | none => 0
    | some (x,_) => (enumerate rows H x ([],0)).1.length*(t+1)) +
    (if reset.isSome then t+1 else 0)

private theorem side_cells_le (lt : α → α → Result Bool) (raise : Bool) (rows : PolylogRows.Rows n t)
    (H : ℕ) (tab : Table α t) (cut : Cut α n) (reset : Option (Fin n)) (v : α) :
    sideCells rows H cut reset ≤ (side lt raise rows H tab cut reset v).work := by
  cases cut with
  | none => cases reset <;> simp [sideCells, side] <;> omega
  | some xc =>
    obtain ⟨x,c⟩ := xc
    have h := edit_cells (PolylogWalls.clamp lt raise c) tab (enumerate rows H x ([],0)).1
    cases reset <;> simp [sideCells, side] <;> omega

def wallCells (next prev : PolylogRows.Rows n t) (H : ℕ) (w : Walls α t) (op : Change α n) : ℕ :=
  let p := (plan w op).value
  sideCells next H p.down p.reset + sideCells prev H p.up p.reset

private theorem wall_cells_le (lt : α → α → Result Bool) (next prev : PolylogRows.Rows n t) (H : ℕ)
    (lo hi : α) (w : Walls α t) (op : Change α n) :
    wallCells next prev H w op ≤ (update lt next prev H lo hi w op).work := by
  let p := (plan w op).value
  have h₁ := side_cells_le lt true next H w.lower p.down p.reset lo
  have h₂ := side_cells_le lt false prev H w.upper p.up p.reset hi
  dsimp only [p] at *
  dsimp only [wallCells,update]
  omega

/-- Count all `cons` constructors in the insertion branch, even if
the compiler can reuse the original list cell. -/
def insertCells (x : Fin n) : List (Fin n) → ℕ
  | [] => 1
  | y :: ys => if x < y then 2 else if x = y then 1 else 1 + insertCells x ys

private theorem insert_cells_le (x : Fin n) (ys : List (Fin n)) :
    insertCells x ys ≤ (insertLabel x ys).work := by
  induction ys with
  | nil => exact Nat.le_succ 1
  | cons y ys ih =>
    simp only [insertCells,insertLabel]
    split_ifs <;> dsimp only <;> omega

private theorem delete_cells_le (x : Fin n) (d : ℕ) (ys : List (Fin n)) :
    (deleteLabel x d ys).value.length ≤ (deleteLabel x d ys).work := by
  induction d generalizing ys with
  | zero => simp [deleteLabel]
  | succ d ih =>
    cases ys with
    | nil => simp [deleteLabel]
    | cons y ys =>
      have h := ih ys
      by_cases eq : y=x <;> simp only [deleteLabel,eq,↓reduceIte,List.length_cons] <;> omega

/-- Deletion rebuilds each surviving list cell and copies one trie path
per affected row. The final reset installs the empty list. -/
def pruneCells (d : ℕ) (tab : PolylogRows.Rows n t) (x : Fin n) : List (Fin n) → ℕ
  | [] => 0
  | y::ys =>
    let items := (deleteLabel x d (tab.get y.val).value).value
    items.length + (t+1) + pruneCells d (tab.put y.val items).value x ys

private theorem prune_cells_le (d : ℕ) (tab : PolylogRows.Rows n t) (x : Fin n) (xs : List (Fin n)) :
    pruneCells d tab x xs ≤ (PolylogWalls.edit (deleteLabel x d) tab xs).work := by
  induction xs generalizing tab with
  | nil => exact Nat.zero_le _
  | cons y ys ih =>
    let items := (deleteLabel x d (tab.get y.val).value).value
    have tail := ih (tab.put y.val items).value
    have row := delete_cells_le x d (tab.get y.val).value
    dsimp only [items] at tail
    simp only [pruneCells,PolylogWalls.edit,Table.put_work]; omega

def graphCells (g : Graph n t) (d : ℕ) : Change α n → ℕ
  | .arc x y =>
    insertCells y (g.succs.get x.val).value + insertCells x (g.preds.get y.val).value + 2*(t+1)
  | .fix x _ =>
    pruneCells d g.succs x (g.preds.get x.val).value +
      pruneCells d g.preds x (g.succs.get x.val).value + 2*(t+1)
  | _ => 0

private theorem graph_cells_le (g : Graph n t) (d : ℕ) (op : Change α n) :
    graphCells g d op ≤ (graphOp g d op).work := by
  cases op with
  | arc x y =>
    have h₁ := insert_cells_le y (g.succs.get x.val).value
    have h₂ := insert_cells_le x (g.preds.get y.val).value
    simp only [graphCells,graphOp, add, addToRow, Table.put_work]; omega
  | fix x c =>
    have h₁ := prune_cells_le d g.succs x (g.preds.get x.val).value
    have h₂ := prune_cells_le d g.preds x (g.succs.get x.val).value
    simp only [graphCells,graphOp,erase,eraseFrom,Table.put_work]
    omega
  | _ => exact Nat.zero_le _

def coreCells (s : PolylogStorage.State n t) (k : ℕ) (op : Change ℕ n) : ℕ :=
  wallCells s.graph.succs s.graph.preds (ArbitraryLabels.pathHeight k) s.walls op + graphCells s.graph k op

private theorem core_cells_le (lt : ℕ → ℕ → Result Bool) (s : PolylogStorage.State n t) (k lo hi : ℕ)
    (op : Change ℕ n) : coreCells s k op ≤
    (updateCore lt s.graph s.walls k (ArbitraryLabels.pathHeight k) lo hi op).work := by
  have h₁ := wall_cells_le lt s.graph.succs s.graph.preds (ArbitraryLabels.pathHeight k) lo hi s.walls op
  have h₂ := graph_cells_le s.graph k op
  dsimp only [coreCells, updateCore]
  omega

private theorem cursor_cells (s : PolylogStorage.State n t) (x : Fin n) (c : ℕ) :
    (if (PolylogHierarchy.lookup s.directory (s.locations.get x.val).value.id c).value.isSome
      then t+1 else 4*(t+1)) ≤ (moveCursor s x c).work := by
  let p := (s.locations.get x.val).value
  cases hh : (PolylogHierarchy.lookup s.directory p.id c).value <;>
    simp only [p] at hh <;>
    simp only [moveCursor, PolylogHierarchy.getOrCreate, hh, PolylogHierarchy.lookup_work,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Table.put_work, Table.get_work] <;> omega

def moveCells (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m) : ℕ :=
  let p := m.spatial.locations.get x.val
  let c := w.out.addr
  let tab := if (PolylogHierarchy.lookup m.spatial.directory p.value.id c).value.isSome
    then t+1 else 4*(t+1)
  coreCells m.spatial k (.fix x c) + tab

theorem move_cells_le (k : ℕ) (m : Memory n t b) (x : Fin n) (w : WriteResult m) :
    moveCells k m x w ≤ (move k m x w).work := by
  let u := m.withHeap w.out.heap w.out.valid w.out.growth
  have ce := core_cells_le u.less m.spatial k m.zero m.one (.fix x w.out.addr)
  have cu := cursor_cells m.spatial x w.out.addr
  dsimp only [moveCells,move,refineState,Memory.withHeap,u,Memory.less] at *
  omega

def recordCells (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer) : ℕ :=
  coreCells m.spatial k (forRecord (route m.spatial q).value q a)

theorem record_cells_le (k : ℕ) (m : Memory n t b) (q : Query n) (a : Answer) :
    recordCells k m q a ≤ (record k m q a).work := by
  have ce := core_cells_le m.less m.spatial k m.zero m.one (forRecord (route m.spatial q).value q a)
  dsimp only [recordCells,record,recordState]; omega

def selectionCells (D k : ℕ) (q : Query n) : ℕ → Memory n t b → ℕ
  | 0, _ => 0
  | f+1, m =>
    match (check D k m q).value with
    | .answer _ => 0
    | .refine x =>
      let w := writePrefix D m x
      moveCells k m x w + selectionCells D k q f (move k m x w).value

private theorem selection_cells_le (D k : ℕ) (q : Query n) (f : ℕ) (m : Memory n t b) :
    selectionCells D k q f m ≤ (select D k q f m).work := by
  induction f generalizing m with
  | zero => exact Nat.zero_le _
  | succ f ih =>
    cases hh : (check D k m q).value with
    | answer => simp only [selectionCells,select,hh]; exact Nat.zero_le _
    | refine x =>
      have he := ih (move k m x (writePrefix D m x)).value
      have hs := move_cells_le k m x (writePrefix D m x)
      simp only [selectionCells,select,hh]; omega

def repairCells (D k : ℕ) : List (Fin n) → Memory n t b → ℕ
  | [], _ => 0
  | x::xs, m =>
    let w := mint D m x (candidate D k m x).value
    moveCells k m x w + repairCells D k xs (repairMove D k m x).value

private theorem repair_cells_le (D k : ℕ) (xs : List (Fin n)) (m : Memory n t b) :
    repairCells D k xs m ≤ (repairList D k xs m).work := by
  induction xs generalizing m with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have he := ih (repairMove D k m x).value
    have hs := move_cells_le k m x (mint D m x (candidate D k m x).value)
    have step : moveCells k m x (mint D m x (candidate D k m x).value) ≤ (repairMove D k m x).work := by
      dsimp only [repairMove]; omega
    simp only [repairCells,repairList]; omega

def compareCells (D k : ℕ) (m : Memory n t b) (q : Query n) :=
  selectionCells D k q 3 m + match (select D k q 3 m).value with
    | none => 0
    | some (u,a) =>
      let r := (record k u q a).value
      recordCells k u q a + repairCells D k (PolylogRepair.choose r.1.spatial.graph k r.2).value r.1

theorem compare_cells_le (D k : ℕ) (m : Memory n t b) (q : Query n) :
    compareCells D k m q ≤ (PolylogCompare.compare D k m q).work := by
  have se := selection_cells_le D k q 3 m
  cases hs : (select D k q 3 m).value with
  | none => simp only [compareCells, PolylogCompare.compare, hs, Nat.add_zero]; omega
  | some z =>
    obtain ⟨u,a⟩ := z
    let r := (record k u q a).value
    have re := record_cells_le k u q a
    have rr := repair_cells_le D k (PolylogRepair.choose r.1.spatial.graph k r.2).value r.1
    dsimp only [r] at rr
    simp only [compareCells, hs]
    change selectionCells D k q 3 m + (recordCells k u q a + repairCells D k
      (PolylogRepair.choose r.1.spatial.graph k r.2).value r.1) ≤ _
    dsimp only [r]
    simp only [PolylogCompare.compare,hs]; omega

open PolylogExecution

def stepCells (c : Config) : State n c → Query n → ℕ
  | .active (_+1) m,q => if 64 ≤ c.k then compareCells c.binaryPoint c.k m q else 0
  | _,_ => 0

theorem step_cells_le (s : State n (config n)) (q : Query n) :
    stepCells (config n) s q ≤ (step (config n) s q).work := by
  cases s with
  | fallback | frozen => exact Nat.zero_le _
  | active f m =>
    cases f with
    | zero => exact Nat.zero_le _
    | succ f =>
      by_cases hk : 64 ≤ (config n).k
      · have hp : (config n).stageData = PolylogPrepared.Params.stage (config n).k := if_pos hk
        have hh := compare_cells_le (config n).binaryPoint (config n).k m q
        simp only [stepCells, if_pos hk, step,hp, PolylogCached.compare_eq]
        split <;> exact hh.trans (Nat.le_add_right _ 3)
      · simp only [stepCells,if_neg hk]; exact Nat.zero_le _

/-- The eight shared fills at startup cover two incidence rows, two walls,
the two-level child directory, the root ancestor table, and the label cursors. -/
def allocatedCells (c : Config) : History n → ℕ
  | [] => if 64 ≤ c.k then 8*(c.tables+1) else 0
  | o::past => allocatedCells c past + stepCells c (replay c past) o.query

private theorem stopped {c : Config} (eq : c = config n) (active : ActiveRefinement n)
    (hist : History n) (late : Controller.horizon n ≤ hist.length) (q : Query n) :
    stepCells c (replay c hist) q = 0 := by
  subst c
  have rel := replay_relates active hist
  generalize concrete : replay (config n) hist = s at rel ⊢
  generalize ref : (PolylogAdversary.policy n).replay (config n).k hist = u at rel
  cases rel with
  | fallback | frozen => rfl
  | @active m fuel M hk good =>
    obtain ⟨_, _, clock⟩ := PolylogPrecision.replay_active hk hist ref
    have hz : fuel = 0 := by omega
    subst fuel; rfl

theorem allocated_cells_le (active : ActiveRefinement n) (hist : History n) :
    allocatedCells (config n) hist ≤ 8*((config n).tables+1) + preFreezeCharges (config n) hist := by
  induction hist with
  | nil => simp only [allocatedCells,preFreezeCharges,Nat.add_zero]; split <;> omega
  | cons o hist ih =>
    by_cases lt : hist.length < Controller.horizon n
    · simp only [allocatedCells,preFreezeCharges,if_pos lt]
      have hh := step_cells_le (replay (config n) hist) o.query
      omega
    · simp only [allocatedCells,preFreezeCharges,if_neg lt, Nat.add_zero, stopped rfl active hist
        (Nat.le_of_not_gt lt) o.query]
      simpa only [Nat.add_zero] using ih

theorem allocated_cells_polynomial (active : ActiveRefinement n) (C e : ℕ)
    (bounds : ∀ hist : History n, ∀ q : Query n,
      (step (config n) (replay (config n) hist) q).work ≤ C*(Optimal.Parameters.logCap n+1)^e)
    (hist : History n) : allocatedCells (config n) hist ≤ 8*(PolylogResources.tableHeight n+1) +
      C*n*(Optimal.Parameters.logCap n+1)^(e+1) :=
  (allocated_cells_le active hist).trans (Nat.add_le_add_left (preFreezeCharges_polynomial C e bounds hist) _)

/-- Count physical constructors in a current balanced dictionary, counting
both arms even when a runtime uses more sharing. -/
def dictionaryNodes {γ : α → Type} : Std.DTreeMap.Internal.Impl α γ → ℕ
  | .leaf => 0
  | .inner _ _ _ l r => 1 + dictionaryNodes l + dictionaryNodes r

private theorem dictionary_nodes_eq {γ : α → Type} (T : Std.DTreeMap.Internal.Impl α γ)
    (hT : T.Balanced) : dictionaryNodes T = T.size := by
  induction hT with
  | leaf => rfl
  | inner hl hr bal size il ir =>
    simp only [dictionaryNodes, Std.DTreeMap.Internal.Impl.size_inner, il, ir]
    omega

attribute [local instance] lexOrd

/-- The two size fields in the stored-entry theorem match the actual number
of live dictionary tree nodes. The statement holds for temporary heaps too. -/
theorem live_dictionary_nodes (H : PolylogBits.Heap) (hv : H.Valid) :
    dictionaryNodes H.address.inner.inner + dictionaryNodes H.record.inner.inner ≤ 2*H.next := by
  have a : dictionaryNodes H.address.inner.inner = H.address.size :=
    dictionary_nodes_eq _ H.address.inner.wf.balanced
  have r : dictionaryNodes H.record.inner.inner = H.record.size :=
    dictionary_nodes_eq _ H.record.inner.wf.balanced
  rw [a,r]
  have := hv.address_size
  have := hv.record_size
  omega

end SortingAdversary.Continuous.PolylogTrieCharges
