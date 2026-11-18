import SortingAdversary.Continuous.PolylogCompare

/-!
# Comparing with cached stage constants

The driver evaluates the sweep count and digit alphabet once when it enters
an admitted stage. The two loops thread that tuple through the existing
tests. Equality of the entire result transfers both answers and work.
-/

namespace SortingAdversary.Continuous.PolylogCached

open PolylogCompare (Memory move mint writePrefix record)
open PolylogPrepared (Params)
open Optimal.PrimitiveWork (Result)
variable {n t b : ℕ}

def check (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) : Result (PolylogActive.Decision n) :=
  let g := m.spatial.graph
  let walls := m.spatial.walls
  let zero := fun h => m.cache.lookup h false
  PolylogActive.attempt m.spatial.locations m.heap b
    (PolylogPrepared.pairWith g walls m.heap zero b D P)
    (PolylogPrepared.thresholdWith g walls m.heap zero b D P) q

def candidate (D : ℕ) (P : Params) (m : Memory n t b) (x : Fin n) : Result (Option ℚ) :=
  PolylogPrepared.centralWith m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D P x

def repairMove (D : ℕ) (P : Params) (m : Memory n t b) (x : Fin n) : Result (Memory n t b) :=
  let a := candidate D P m x
  let r := move P.k m x (mint D m x a.value)
  ⟨r.value, a.work + r.work + 1⟩

def select (D : ℕ) (P : Params) (q : Query n) : ℕ → Memory n t b → Result (Option (Memory n t b × Answer))
  | 0, _ => ⟨none,1⟩
  | fuel+1, m =>
    let a := check D P m q
    match a.value with
    | .answer b => ⟨some (m,b),a.work+2⟩
    | .refine x =>
      let r := move P.k m x (writePrefix D m x)
      let more := select D P q fuel r.value
      ⟨more.value, a.work+r.work+more.work+3⟩

def repairList (D : ℕ) (P : Params) : List (Fin n) → Memory n t b → Result (Memory n t b)
  | [], m => ⟨m,1⟩
  | x :: xs, m =>
    let r := repairMove D P m x
    let more := repairList D P xs r.value
    ⟨more.value,r.work+more.work+2⟩

def compare (D : ℕ) (P : Params) (m : Memory n t b) (q : Query n) : Result (Option (Memory n t b × Answer)) :=
  let s := select D P q 3 m
  match s.value with
  | none => ⟨none,s.work+1⟩
  | some (u,a) =>
    let r := record P.k u q a
    let path := PolylogRepair.choose r.value.1.spatial.graph P.k r.value.2
    let next := repairList D P path.value r.value.1
    ⟨some (next.value,a),s.work + r.work + path.work + next.work + 4⟩


theorem check_eq (D k : ℕ) (m : Memory n t b) (q : Query n) :
    check D (.stage k) m q = PolylogCompare.check D k m q := rfl

theorem repairMove_eq (D k : ℕ) (m : Memory n t b) (x : Fin n) :
    repairMove D (.stage k) m x = PolylogCompare.repairMove D k m x := rfl

private theorem stage_k (k : ℕ) : (Params.stage k).k = k := rfl

theorem select_eq (D k : ℕ) (q : Query n) (f : ℕ) (m : Memory n t b) :
    select D (.stage k) q f m = PolylogCompare.select D k q f m := by
  induction f generalizing m with
  | zero => rfl
  | succ f ih =>
    simp only [select, PolylogCompare.select, check_eq, ih, stage_k]
    cases (PolylogCompare.check D k m q).value <;> rfl

theorem repairList_eq (D k : ℕ) (xs : List (Fin n)) (m : Memory n t b) :
    repairList D (.stage k) xs m = PolylogCompare.repairList D k xs m := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    simp only [repairList, PolylogCompare.repairList, repairMove_eq, ih]

theorem compare_eq (D k : ℕ) (m : Memory n t b) (q : Query n) :
    compare D (.stage k) m q = PolylogCompare.compare D k m q := by
  simp only [compare, PolylogCompare.compare, select_eq, repairList_eq, stage_k]
  cases (PolylogCompare.select D k q 3 m).value with
  | none => rfl
  | some a => cases a; rfl

end SortingAdversary.Continuous.PolylogCached
