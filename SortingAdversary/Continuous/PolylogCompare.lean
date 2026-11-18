import SortingAdversary.Continuous.PolylogMemory
import SortingAdversary.Continuous.PolylogActive
import SortingAdversary.Continuous.PolylogMutation
import SortingAdversary.Continuous.PolylogRecordProof
import SortingAdversary.Continuous.PolylogPreparedDefs
import SortingAdversary.Continuous.PolylogRawAnchor

/-!
# An active query on stored rows, cursors, and dyadic addresses

Selection has three trials. An unsuccessful trial writes the exact prefix
anchor and moves one label; a successful trial records the answer. The
recorded arc, if any, determines where to look for the repair. The loop
updates the same heap and sparse tables after each reserved move.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open PolylogBits PolylogAnchorWrite
open Optimal.PrimitiveWork (Result)
open TreeState (Routing)
variable {n t b : ℕ}

/-- A successful short test or failed-test prefix, with the new persistent
heap. Storing the word-sized address here keeps the rational interpretation
out of all selection and repair loops. -/
structure WriteResult (m : Memory n t b) where
  out : Written m.heap
  work : ℕ

/-- Commit a new anchor handle in the enlarged heap, update the two wall
rows and incidence lists, and move the label's cursor. -/
def move (k : ℕ) (m : Memory n t b) (x : Fin n) (mint : WriteResult m) : Result (Memory n t b) :=
  let m' := m.withHeap mint.out.heap mint.out.valid mint.out.growth
  let r := PolylogMutation.refineState m'.less m'.spatial k m'.zero m'.one x mint.out.addr
  ⟨{m' with spatial := r.value}, mint.work+r.work+2⟩

def check (D k : ℕ) (m : Memory n t b) (q : Query n) : Result (PolylogActive.Decision n) :=
  let g := m.spatial.graph
  let walls := m.spatial.walls
  let zero := fun h => m.cache.lookup h false
  PolylogActive.attempt m.spatial.locations m.heap b
    (PolylogPrepared.pair g walls m.heap zero b D k)
    (PolylogPrepared.threshold g walls m.heap zero b D k) q

def candidate (D k : ℕ) (m : Memory n t b) (x : Fin n) : Result (Option ℚ) :=
  PolylogPrepared.central m.spatial.graph m.spatial.walls m.heap (fun h => m.cache.lookup h false) b D k x

def writePrefix (D : ℕ) (m : Memory n t b) (x : Fin n) : WriteResult m :=
  let l := m.spatial.walls.lower.get x.val
  let r := m.spatial.walls.upper.get x.val
  let z := PolylogRawAnchor.fallback D (D - 2) m.valid m.typed m.cache (le_refl b) l.value r.value
  ⟨⟨z.heap,z.addr,z.valid,z.growth⟩,l.work+r.work+z.work+2⟩

def mint (D : ℕ) (m : Memory n t b) (x : Fin n) : Option ℚ → WriteResult m
  | none => writePrefix D m x
  | some q =>
    let e := Optimal.Parameters.logCap n
    let w := PolylogEmbed.embedAddr D e (numerator q e) m.valid m.cache (le_refl b)
    ⟨Written.ofWrite w.toWrite, w.work + e + 4⟩

def repairMove (D k : ℕ) (m : Memory n t b) (x : Fin n) : Result (Memory n t b) :=
  let a := candidate D k m x
  let r := move k m x (mint D m x a.value)
  ⟨r.value, a.work + r.work + 1⟩

def select (D k : ℕ) (q : Query n) : ℕ → Memory n t b → Result (Option (Memory n t b × Answer))
  | 0, _ => ⟨none,1⟩
  | fuel+1, m =>
    let a := check D k m q
    match a.value with
    | .answer b => ⟨some (m,b),a.work+2⟩
    | .refine x =>
      let r := move k m x (writePrefix D m x)
      let more := select D k q fuel r.value
      ⟨more.value, a.work+r.work+more.work+3⟩

def repairList (D k : ℕ) : List (Fin n) → Memory n t b → Result (Memory n t b)
  | [], m => ⟨m,1⟩
  | x :: xs, m =>
    let r := repairMove D k m x
    let more := repairList D k xs r.value
    ⟨more.value,r.work+more.work+2⟩

def compare (D k : ℕ) (m : Memory n t b) (q : Query n) : Result (Option (Memory n t b × Answer)) :=
  let s := select D k q 3 m
  match s.value with
  | none => ⟨none,s.work+1⟩
  | some (u,a) =>
    let r := record k u q a
    let path := PolylogRepair.choose r.value.1.spatial.graph k r.value.2
    let next := repairList D k path.value r.value.1
    ⟨some (next.value,a),s.work + r.work + path.work + next.work + 4⟩

end SortingAdversary.Continuous.PolylogCompare
