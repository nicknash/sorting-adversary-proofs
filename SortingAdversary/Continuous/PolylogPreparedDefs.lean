import SortingAdversary.Continuous.PolylogNeighborhood
import SortingAdversary.Continuous.PolylogRepair
import SortingAdversary.Continuous.PolylogWallTables
import SortingAdversary.Continuous.PolylogOracleWork
import SortingAdversary.Continuous.PolylogOracle

/-!
# Local tests from sparse graph rows and wall addresses

Each call discovers its retained labels from the original adjacency rows.
After reindexing, the address gathers and digit sweeps operate on vectors of
that local size. Query indices are recovered by scanning the local embedding.
-/

namespace SortingAdversary.Continuous.PolylogPrepared

open PolylogNeighborhood PolylogRows PolylogWallTables PolylogBits FiniteAveraging
open Optimal
open Optimal.PrimitiveWork (Result)
open PolylogOracle (grid cutoff)
open ArbitraryLabels (pathHeight widthThreshold_pos)
open EnclosureParameters (alphabetExponent)
variable {n m h : ℕ}

def reads (g : Graph n h) : Reads n :=
  ⟨fun _ => ⟨0,1⟩, fun _ => ⟨0,1⟩, fun x => (g.succs.get x.val).value⟩

abbrev adjacent (g : Graph n h) := PolylogRepair.adjacent g

theorem reads_edge (g : Graph n h) (D : System (Fin n) ℚ) (hg : g.Valid D.edge) :
    (reads g).system.edge = D.edge := by
  funext x y
  simp [reads, Reads.system, hg.1]

theorem adjacent_mem (g : Graph n h) (D : System (Fin n) ℚ) (hg : g.Valid D.edge)
    (hl : ∀ x, D.edge x x = false) (x y : Fin n) :
    y ∈ adjacent g x ↔ y ∈ GraphBalls.neighbors D.edge x := by
  exact PolylogRepair.adjacent_mem g hg hl x y

def addresses (w : Walls ℕ h) (v : Vector (Fin n) m) : Result (Vector ℕ m × Vector ℕ m) :=
  let lo := PrimitiveWork.vector (fun i => w.lower.get v[i].val)
  let hi := PrimitiveWork.vector (fun i => w.upper.get v[i].val)
  ⟨(lo.value,hi.value),lo.work+hi.work+2⟩

theorem addresses_work (w : Walls ℕ h) (v : Vector (Fin n) m) :
    (addresses w v).work ≤ 2*m*(4*h+3)+2 := by
  have lo := PrimitiveWork.vector_work_le (fun i : Fin m => w.lower.get v[i].val) (4*h+1)
    (fun i => (PolylogRouting.Table.get_work ..).le)
  have hi := PrimitiveWork.vector_work_le (fun i : Fin m => w.upper.get v[i].val) (4*h+1)
    (fun i => (PolylogRouting.Table.get_work ..).le)
  dsimp only [addresses]
  nlinarith

def withIndex (p : Prepared n m) (x : Fin n) (f : Fin m → Result (Option α)) :
    Result (Option α) :=
  let idx := queryIndex p.embedding x
  let t := match idx.value with
    | some i => f i
    | none => ⟨none,0⟩
  ⟨t.value,idx.work+t.work+2⟩

theorem withIndex_eq (p : Prepared n m) (e : Fin m ↪ Fin n)
    (he : ∀ i, p.embedding[i] = e i) (x : Fin n) (i : Fin m) (hi : e i = x)
    (f : Fin m → Result (Option α)) :
    withIndex p x f = ⟨(f i).value, (queryIndex p.embedding x).work+(f i).work+2⟩ := by
  subst x
  simp [withIndex,queryIndex_value p.embedding e he i]

/-- Apply the scalar kernel only after building the actual small short-wall address vectors. -/
def withWalls (w : Walls ℕ h) (p : Prepared n m)
    (f : Vector ℕ m → Vector ℕ m → Result α) : Result α :=
  let a := addresses w p.embedding
  let t := f a.value.1 a.value.2
  ⟨t.value, a.work+t.work+1⟩

abbrev halfWidth (k : ℕ) := cutoff k / 2
theorem width_pos (k : ℕ) : 0 < halfWidth k := half_pos (widthThreshold_pos ..)

/-- Stage data cached before the online comparisons. -/
structure Params where
  k : ℕ
  height : ℕ
  sweeps : ℕ
  grid : ℕ
  exponent : ℕ

def Params.stage (k : ℕ) : Params :=
  ⟨k, pathHeight k, if hk : 0 < k then Neighborhood.sweeps k (pathHeight k) hk
    (halfWidth k) (width_pos k) else 0, PolylogOracle.grid k, alphabetExponent k (pathHeight k)⟩

def pairAtWith (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
    (x y : Fin n) (p : Prepared n m) : Result (Option Answer) :=
  withIndex p x fun i => withIndex p y fun j => withWalls w p fun lo hi =>
    PolylogOracleWork.heapPair heap zero level D P.grid P.exponent
      lo hi p.data.edge p.schedule P.k i j

def thresholdAtWith (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
    (x : Fin n) (addr : ℕ) (p : Prepared n m) : Result (Option Answer) :=
  withIndex p x fun i => withWalls w p fun lo hi =>
    PolylogOracleWork.heapThreshold heap zero level D P.grid P.exponent
      lo hi p.data.edge p.schedule P.k i addr

def centralAtWith (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ) (P : Params)
    (x : Fin n) (p : Prepared n m) : Result (Option ℚ) :=
  withIndex p x fun i => withWalls w p fun lo hi =>
    PolylogOracleWork.heapCentral heap zero level D P.grid P.exponent
      lo hi p.data.edge p.schedule i

abbrev pairAt (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D k : ℕ)
    (x y : Fin n) (p : Prepared n m) := pairAtWith w heap zero level D (Params.stage k) x y p

abbrev thresholdAt (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D k : ℕ)
    (x : Fin n) (addr : ℕ) (p : Prepared n m) := thresholdAtWith w heap zero level D (Params.stage k) x addr p

abbrev centralAt (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D k : ℕ)
    (x : Fin n) (p : Prepared n m) := centralAtWith w heap zero level D (Params.stage k) x p

/-- The same graph access charge covers two row fetches and copying an
outgoing row of length at most the current degree cap. -/
def runWith (g : Graph n h) (P : Params) (roots : List (Fin n))
    (f : ∀ {m}, Prepared n m → Result (Option α)) : Result (Option α) :=
  if 0 < P.k then
    withPrepared (reads g) (adjacent g) roots (P.height*P.sweeps) P.sweeps (8*h+2*P.k+10) f
  else ⟨none,1⟩

abbrev run (g : Graph n h) (k : ℕ) (roots : List (Fin n))
    (f : ∀ {m}, Prepared n m → Result (Option α)) :=
  runWith g (Params.stage k) roots f

def pairWith (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x y : Fin n) := runWith g P [x,y] (pairAtWith w heap zero level D P x y)

abbrev pair (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D k : ℕ)
    (x y : Fin n) := pairWith g w heap zero level D (Params.stage k) x y

def thresholdWith (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x : Fin n) (addr : ℕ) := runWith g P [x] (thresholdAtWith w heap zero level D P x addr)

abbrev threshold (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D k : ℕ)
    (x : Fin n) (addr : ℕ) := thresholdWith g w heap zero level D (Params.stage k) x addr

def centralWith (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D : ℕ)
    (P : Params) (x : Fin n) := runWith g P [x] (centralAtWith w heap zero level D P x)

abbrev central (g : Graph n h) (w : Walls ℕ h) (heap : Heap) (zero : ℕ → ℕ) (level D k : ℕ)
    (x : Fin n) := centralWith g w heap zero level D (Params.stage k) x

end SortingAdversary.Continuous.PolylogPrepared
