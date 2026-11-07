import SortingAdversary.Optimal.FiniteLoopWork
import SortingAdversary.Optimal.SparseRepairGraph
import SortingAdversary.Optimal.RankWork
import SortingAdversary.Optimal.ClosureWork

/-!
# Measured longest-path tables and compressed height ranks

The routines below retain the deterministic first-longest tie rule of
`SparseRepairGraph`. The counter includes finite-index generation, candidate
filtering, table reads, both path-length traversals at every comparison,
rank evaluation, and every vector layer. Row and rank callbacks report their
own costs. Strict topological ranks imply that every stored path has at most
`n` labels, which discharges the list-length parameters of the work bound.
-/

namespace SortingAdversary.Optimal.LongestPathWork

open PrimitiveWork SparseRepairGraph GraphBalls

variable {α : Type*} {n : ℕ}

abbrev Rows (n : ℕ) := Fin n → Fin n → Result Bool
abbrev Rank (n : ℕ) := Fin n → Result ℕ

def rowValues (rows : Rows n) : Fin n → Fin n → Bool := fun u v => (rows u v).value
def rankValues (rank : Rank n) : Fin n → ℕ := fun v => (rank v).value

def longest : List (List α) → Result (List α)
  | [] => ⟨[], 1⟩
  | path :: paths =>
      let tail := longest paths
      let tailLength := FiniteLoopWork.length tail.value
      let pathLength := FiniteLoopWork.length path
      ⟨if tailLength.value ≤ pathLength.value then path else tail.value,
        tail.work + tailLength.work + pathLength.work + 3⟩

@[simp] theorem longest_value (paths : List (List α)) :
    (longest paths).value = SparseRepairGraph.longest paths := by
  induction paths with
  | nil => rfl
  | cons path paths ih =>
      simp only [longest, FiniteLoopWork.length_value, ih, SparseRepairGraph.longest]

theorem longest_length_le (paths : List (List α)) (bound : ℕ)
    (h : ∀ path ∈ paths, path.length ≤ bound) : (longest paths).value.length ≤ bound := by
  rw [longest_value]
  rcases longest_selected paths with he | hm
  · simp [he]
  · exact h _ hm

theorem longest_work_le (paths : List (List α)) (bound : ℕ)
    (h : ∀ path ∈ paths, path.length ≤ bound) :
    (longest paths).work ≤ paths.length * (4 * bound + 5) + 1 := by
  induction paths with
  | nil => simp [longest]
  | cons path paths ih =>
      have hp := h path (List.mem_cons_self ..)
      have ht : ∀ q ∈ paths, q.length ≤ bound := fun q hq => h q (List.mem_cons_of_mem path hq)
      have hi := ih ht
      have hl := longest_length_le paths bound ht
      simp only [longest, FiniteLoopWork.length_work, List.length_cons, Nat.add_mul, one_mul]
      omega

def incoming (rows : Rows n) (v u : Fin n) : Result Bool :=
  let edge := rows u v
  ⟨decide (u ≠ v) && edge.value, edge.work + 2⟩

def candidates (rows : Rows n) (table : PathTable n) (v : Fin n) : Result (List (List (Fin n))) :=
  let domain := FiniteLoopWork.indices n
  let selected := FiniteLoopWork.filter (incoming rows v) domain.value
  let result := PrimitiveWork.map (fun u => atom table[u]) selected.value
  ⟨result.value, domain.work + selected.work + result.work⟩

@[simp] theorem candidates_value (rows : Rows n) (table : PathTable n) (v : Fin n) :
    (candidates rows table v).value = SparseRepairGraph.candidates (rowValues rows) table v := by
  simp only [candidates, FiniteLoopWork.indices, FiniteLoopWork.filter_value,
    PrimitiveWork.map_value, incoming, atom, SparseRepairGraph.candidates, rowValues]

theorem candidates_length_le (rows : Rows n) (table : PathTable n) (v : Fin n) :
    (candidates rows table v).value.length ≤ n := by
  rw [candidates_value]
  simpa only [SparseRepairGraph.candidates, List.length_map, List.length_finRange] using
    List.length_filter_le (fun u => decide (u ≠ v) && rowValues rows u v) (List.finRange n)

theorem candidates_paths_le (rows : Rows n) (table : PathTable n) (v : Fin n) (bound : ℕ)
    (h : ∀ u : Fin n, (table[u]).length ≤ bound) :
    ∀ path ∈ (candidates rows table v).value, path.length ≤ bound := by
  intro path hp
  rw [candidates_value] at hp
  obtain ⟨u, _, rfl⟩ := (mem_candidates _ _ _ _).mp hp
  exact h u

theorem candidates_work_le (rows : Rows n) (table : PathTable n) (v : Fin n) (bound : ℕ)
    (h : ∀ u v, (rows u v).work ≤ bound) :
    (candidates rows table v).work ≤ n * (bound + 11) + 3 := by
  have hf := FiniteLoopWork.filter_work_le (incoming rows v) (List.finRange n) (bound + 2)
    (fun u _ => Nat.add_le_add_right (h u v) 2)
  have hm := PrimitiveWork.map_work_le (fun u => atom table[u])
    (FiniteLoopWork.filter (incoming rows v) (List.finRange n)).value 1 (fun _ _ => le_rfl)
  have hlen : (FiniteLoopWork.filter (incoming rows v) (List.finRange n)).value.length ≤ n := by
    rw [FiniteLoopWork.filter_value]
    simpa only [List.length_finRange] using List.length_filter_le _ (List.finRange n)
  have hm' := hm.trans (Nat.add_le_add_right (Nat.mul_le_mul_right 3 hlen) 1)
  simp only [List.length_finRange] at hf
  change (3 * n + 1) +
    (FiniteLoopWork.filter (incoming rows v) (List.finRange n)).work +
    (PrimitiveWork.map (fun u => atom table[u])
      (FiniteLoopWork.filter (incoming rows v) (List.finRange n)).value).work ≤ _
  calc
    _ ≤ (3 * n + 1) + (n * ((bound + 2) + 3) + 1) + (n * 3 + 1) := by omega
    _ = _ := by ring

def pathCell (rows : Rows n) (rank : Rank n) (k : ℕ) (table : PathTable n) (v : Fin n) :
    Result (List (Fin n)) :=
  let position := rank v
  if position.value = k then
    let choices := candidates rows table v
    let best := longest choices.value
    ⟨v :: best.value, position.work + choices.work + best.work + 3⟩
  else ⟨table[v], position.work + 2⟩

@[simp] theorem pathCell_value (rows : Rows n) (rank : Rank n) (k : ℕ)
    (table : PathTable n) (v : Fin n) :
    (pathCell rows rank k table v).value =
      if rankValues rank v = k then
        v :: SparseRepairGraph.longest (SparseRepairGraph.candidates (rowValues rows) table v)
      else table[v] := by
  simp only [pathCell, rankValues]
  split <;> simp_all [longest_value, candidates_value]

theorem pathCell_work_le (rows : Rows n) (rank : Rank n) (k : ℕ) (table : PathTable n)
    (v : Fin n) (rowWork rankWork length : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hlength : ∀ u : Fin n, (table[u]).length ≤ length) :
    (pathCell rows rank k table v).work ≤ rankWork + n * (rowWork + 4 * length + 16) + 7 := by
  have hp := hrank v
  have hc := candidates_work_le rows table v rowWork hrows
  have hb := longest_work_le (candidates rows table v).value length
    (candidates_paths_le rows table v length hlength)
  have hn := candidates_length_le rows table v
  have hb' := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [pathCell]
  split
  · dsimp only
    calc
      _ ≤ rankWork + (n * (rowWork + 11) + 3) + (n * (4 * length + 5) + 1) + 3 := by omega
      _ = _ := by ring
  · dsimp only
    omega

def pathStep (rows : Rows n) (rank : Rank n) (k : ℕ) (table : PathTable n) : Result (PathTable n) :=
  PrimitiveWork.vector (pathCell rows rank k table)

@[simp] theorem pathStep_value (rows : Rows n) (rank : Rank n) (k : ℕ) (table : PathTable n) :
    (pathStep rows rank k table).value = SparseRepairGraph.pathStep (rowValues rows) (rankValues rank) k table := by
  simp only [pathStep, PrimitiveWork.vector_value, pathCell_value, SparseRepairGraph.pathStep]

theorem pathStep_work_le (rows : Rows n) (rank : Rank n) (k : ℕ) (table : PathTable n)
    (rowWork rankWork length : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hlength : ∀ u : Fin n, (table[u]).length ≤ length) :
    (pathStep rows rank k table).work ≤ n * (rankWork + n * (rowWork + 4 * length + 16) + 9) := by
  simpa only [pathStep, Nat.add_assoc, Nat.reduceAdd] using PrimitiveWork.vector_work_le
    (pathCell rows rank k table) (rankWork + n * (rowWork + 4 * length + 16) + 7)
    (fun v => pathCell_work_le rows rank k table v rowWork rankWork length hrows hrank hlength)

def pathTable (rows : Rows n) (rank : Rank n) : ℕ → Result (PathTable n)
  | 0 => ⟨Vector.replicate n [], n + 1⟩
  | k + 1 =>
      let previous := pathTable rows rank k
      let result := pathStep rows rank k previous.value
      ⟨result.value, previous.work + result.work + 1⟩

@[simp] theorem pathTable_value (rows : Rows n) (rank : Rank n) (k : ℕ) :
    (pathTable rows rank k).value = SparseRepairGraph.pathTable (rowValues rows) (rankValues rank) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pathTable, pathStep_value, ih, SparseRepairGraph.pathTable]

def tableBound (n layers rowWork rankWork : ℕ) : ℕ :=
  n + 1 + layers * (n * (rankWork + n * (rowWork + 4 * n + 16) + 9) + 1)

theorem pathTable_work_le (rows : Rows n) (rank : Rank n) (k rowWork rankWork : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (pathTable rows rank k).work ≤ tableBound n k rowWork rankWork := by
  induction k with
  | zero => simp [pathTable, tableBound]
  | succ k ih =>
      have hs := pathStep_work_le rows rank k (pathTable rows rank k).value
        rowWork rankWork n hrows hrank (by
          intro v
          rw [pathTable_value]
          exact stored_path_length_le _ _ hstrict k v)
      simp only [pathTable, tableBound, Nat.add_mul, one_mul] at ih ⊢
      omega

def longestChain (rows : Rows n) (rank : Rank n) (bound : ℕ) : Result (List (Fin n)) :=
  let table := pathTable rows rank bound
  let domain := FiniteLoopWork.indices n
  let paths := PrimitiveWork.map (fun v => atom table.value[v]) domain.value
  let result := longest paths.value
  ⟨result.value, table.work + domain.work + paths.work + result.work⟩

@[simp] theorem longestChain_value (rows : Rows n) (rank : Rank n) (bound : ℕ) :
    (longestChain rows rank bound).value =
      SparseRepairGraph.longestChain (rowValues rows) (rankValues rank) bound := by
  simp only [longestChain, longest_value, PrimitiveWork.map_value, atom, FiniteLoopWork.indices,
    pathTable_value, SparseRepairGraph.longestChain]

theorem longestChain_length_le (rows : Rows n) (rank : Rank n) (bound : ℕ)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (longestChain rows rank bound).value.length ≤ n := by
  apply longest_length_le
  simp only [PrimitiveWork.map_value, FiniteLoopWork.indices, atom, List.mem_map]
  rintro path ⟨v, _, rfl⟩
  rw [pathTable_value]
  exact stored_path_length_le _ _ hstrict bound v

def chainBound (n layers rowWork rankWork : ℕ) : ℕ :=
  tableBound n layers rowWork rankWork + n * (4 * n + 11) + 3

theorem longestChain_work_le (rows : Rows n) (rank : Rank n) (bound rowWork rankWork : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (longestChain rows rank bound).work ≤ chainBound n bound rowWork rankWork := by
  have ht := pathTable_work_le rows rank bound rowWork rankWork hrows hrank hstrict
  have hm := PrimitiveWork.map_work_le (fun v => atom (pathTable rows rank bound).value[v])
    (List.finRange n) 1 (fun _ _ => le_rfl)
  have hl := longest_work_le
    (PrimitiveWork.map (fun v => atom (pathTable rows rank bound).value[v]) (List.finRange n)).value n (by
      simp only [PrimitiveWork.map_value, atom, List.mem_map]
      rintro path ⟨v, _, rfl⟩
      rw [pathTable_value]
      exact stored_path_length_le _ _ hstrict bound v)
  rw [show (PrimitiveWork.map (fun v => atom (pathTable rows rank bound).value[v])
    (List.finRange n)).value.length = n by simp only [PrimitiveWork.map_value, List.length_map,
      List.length_finRange]] at hl
  simp only [List.length_finRange, Nat.reduceAdd] at hm
  dsimp only [longestChain, FiniteLoopWork.indices]
  unfold chainBound
  calc
    _ ≤ tableBound n bound rowWork rankWork + (3 * n + 1) + (n * 3 + 1) + (n * (4 * n + 5) + 1) := by omega
    _ = _ := by ring

def heightRanks (rows : Rows n) (rank : Rank n) (bound : ℕ) : Result (Vector ℕ n) :=
  let table := pathTable rows rank bound
  let result := PrimitiveWork.vector (fun v =>
    let length := FiniteLoopWork.length table.value[v]
    ⟨length.value - 1, length.work + 2⟩)
  ⟨result.value, table.work + result.work⟩

@[simp] theorem heightRanks_value (rows : Rows n) (rank : Rank n) (bound : ℕ) :
    (heightRanks rows rank bound).value =
      Vector.ofFn (SparseRepairGraph.heightRank (rowValues rows) (rankValues rank) bound) := by
  simp only [heightRanks, PrimitiveWork.vector_value, FiniteLoopWork.length_value,
    pathTable_value, SparseRepairGraph.heightRank]

theorem heightRanks_work_le (rows : Rows n) (rank : Rank n) (bound rowWork rankWork : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (heightRanks rows rank bound).work ≤ tableBound n bound rowWork rankWork + n * (2 * n + 5) := by
  have ht := pathTable_work_le rows rank bound rowWork rankWork hrows hrank hstrict
  have hv := PrimitiveWork.vector_work_le (fun v : Fin n =>
    let length := FiniteLoopWork.length (pathTable rows rank bound).value[v]
    (⟨length.value - 1, length.work + 2⟩ : Result ℕ)) (2 * n + 3) (by
      intro v
      have hl : ((pathTable rows rank bound).value[v]).length ≤ n := by
        rw [pathTable_value]
        exact stored_path_length_le _ _ hstrict bound v
      dsimp only
      rw [FiniteLoopWork.length_work]
      omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hv
  exact Nat.add_le_add ht hv

def heightRank (rows : Rows n) (rank : Rank n) (bound : ℕ) : Result (Fin n → ℕ) :=
  let cached := heightRanks rows rank bound
  ⟨fun v => cached.value[v], cached.work⟩

@[simp] theorem heightRank_value (rows : Rows n) (rank : Rank n) (bound : ℕ) :
    (heightRank rows rank bound).value =
      SparseRepairGraph.heightRank (rowValues rows) (rankValues rank) bound := by
  funext v
  simp only [heightRank, heightRanks_value, Fin.getElem_fin, Vector.getElem_ofFn]

def height (rows : Rows n) (rank : Rank n) (bound : ℕ) : Result ℕ :=
  let chain := longestChain rows rank bound
  let result := FiniteLoopWork.length chain.value
  ⟨result.value, chain.work + result.work⟩

@[simp] theorem height_value (rows : Rows n) (rank : Rank n) (bound : ℕ) :
    (height rows rank bound).value =
      SparseRepairGraph.height (rowValues rows) (rankValues rank) bound := by
  simp only [height, FiniteLoopWork.length_value, longestChain_value, SparseRepairGraph.height]

theorem height_work_le (rows : Rows n) (rank : Rank n) (bound rowWork rankWork : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (height rows rank bound).work ≤ chainBound n bound rowWork rankWork + 2 * n + 1 := by
  have hc := longestChain_work_le rows rank bound rowWork rankWork hrows hrank hstrict
  have hl := longestChain_length_le rows rank bound hstrict
  simp only [height, FiniteLoopWork.length_work]
  omega

def take : ℕ → List α → Result (List α)
  | 0, _ => ⟨[], 1⟩
  | _ + 1, [] => ⟨[], 1⟩
  | k + 1, x :: xs =>
      let rest := take k xs
      ⟨x :: rest.value, rest.work + 3⟩

@[simp] theorem take_value (count : ℕ) (xs : List α) : (take count xs).value = xs.take count := by
  induction xs generalizing count with
  | nil => cases count <;> rfl
  | cons x xs ih => cases count <;> simp [take, ih]

theorem take_work_le (count : ℕ) (xs : List α) : (take count xs).work ≤ 3 * xs.length + 1 := by
  induction xs generalizing count with
  | nil => cases count <;> simp [take]
  | cons x xs ih =>
      cases count with
      | zero => simp [take]
      | succ count => have h := ih count; simp only [take, List.length_cons]; omega

def reserve (rows : Rows n) (rank : Rank n) (bound count : ℕ) : Result (List (Fin n)) :=
  let chain := longestChain rows rank bound
  let result := take count chain.value
  ⟨result.value, chain.work + result.work⟩

@[simp] theorem reserve_value (rows : Rows n) (rank : Rank n) (bound count : ℕ) :
    (reserve rows rank bound count).value =
      SparseRepairGraph.reserve (rowValues rows) (rankValues rank) bound count := by
  simp only [reserve, take_value, longestChain_value, SparseRepairGraph.reserve]

theorem reserve_work_le (rows : Rows n) (rank : Rank n) (bound count rowWork rankWork : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (reserve rows rank bound count).work ≤ chainBound n bound rowWork rankWork + 3 * n + 1 := by
  have hc := longestChain_work_le rows rank bound rowWork rankWork hrows hrank hstrict
  have hl := longestChain_length_le rows rank bound hstrict
  have ht := take_work_le count (longestChain rows rank bound).value
  change _ + _ ≤ _
  omega

theorem heightRank_work_le (rows : Rows n) (rank : Rank n) (bound rowWork rankWork : ℕ)
    (hrows : ∀ u v, (rows u v).work ≤ rowWork) (hrank : ∀ u, (rank u).work ≤ rankWork)
    (hstrict : ∀ u v, Arc (rowValues rows) u v → rankValues rank u < rankValues rank v) :
    (heightRank rows rank bound).work ≤ tableBound n bound rowWork rankWork + n * (2 * n + 5) :=
  heightRanks_work_le rows rank bound rowWork rankWork hrows hrank hstrict

/-- A cached public ranking followed by the actual longest-path compression
used by `NormalizedBounds.readyBounds`. -/
def normalizedRank (publicRows : RankWork.Rows n) (activeRows : Rows n) : Result (Vector ℕ n) :=
  let publicCached := RankWork.ranks publicRows
  let compressed := heightRanks activeRows (fun v => ⟨publicCached.value[v].val, 1⟩) n
  ⟨compressed.value, publicCached.work + compressed.work⟩

theorem cached_publicRank (s : WidthRepair.State n) (rows : RankWork.Rows n)
    (hrows : RankWork.values rows = s.pool.system.edge) :
    rankValues (fun v : Fin n => (⟨(RankWork.ranks rows).value[v].val, 1⟩ : Result ℕ)) =
      NormalizedBounds.publicRank s := by
  funext v
  simp only [rankValues, RankWork.ranks_value, Fin.getElem_fin, Vector.getElem_ofFn,
    hrows, NormalizedBounds.publicRank_eq]

theorem normalizedRank_value (s : WidthRepair.State n) (publicRows : RankWork.Rows n) (activeRows : Rows n)
    (hpublic : RankWork.values publicRows = s.pool.system.edge)
    (hactive : rowValues activeRows = s.rows.active) :
    (normalizedRank publicRows activeRows).value = Vector.ofFn (NormalizedBounds.rank s) := by
  simp only [normalizedRank, heightRanks_value, hactive, cached_publicRank s publicRows hpublic]
  rfl

theorem normalizedRank_work_le (s : WidthRepair.State n) (publicRows : RankWork.Rows n) (activeRows : Rows n)
    (hpublic : RankWork.values publicRows = s.pool.system.edge)
    (hactive : rowValues activeRows = s.rows.active) (publicWork activeWork : ℕ)
    (hp : ∀ u v, (publicRows u v).work ≤ publicWork)
    (ha : ∀ u v, (activeRows u v).work ≤ activeWork) :
    (normalizedRank publicRows activeRows).work ≤
      RankWork.workBound n publicWork + tableBound n n activeWork 1 + n * (2 * n + 5) := by
  have hstrict : ∀ u v, Arc (rowValues activeRows) u v →
      rankValues (fun v : Fin n => (⟨(RankWork.ranks publicRows).value[v].val, 1⟩ : Result ℕ)) u <
        rankValues (fun v : Fin n => (⟨(RankWork.ranks publicRows).value[v].val, 1⟩ : Result ℕ)) v := by
    rw [cached_publicRank s publicRows hpublic, hactive]
    exact NormalizedBounds.publicRank_strict s
  have hr := RankWork.ranks_work_le publicRows publicWork hp
  have hh := heightRanks_work_le activeRows
    (fun v : Fin n => ⟨(RankWork.ranks publicRows).value[v].val, 1⟩)
    n activeWork 1 ha (fun _ => le_rfl) hstrict
  change _ + _ ≤ _
  omega

/-- Materialize the shifted rank vector once after insertion of a physical
comparison. The Floyd closure and input rank getters report all their work. -/
def ranksAfterAdd (rows : Rows n) (rank : Rank n) (height : ℕ) (head : Fin n) : Result (Vector ℕ n) :=
  let reach := ClosureWork.closure rows
  let result := PrimitiveWork.vector (fun v =>
    let old := rank v
    ⟨old.value + if reach.value[head][v] = true then height else 0, old.work + 4⟩)
  ⟨result.value, reach.work + result.work⟩

@[simp] theorem ranksAfterAdd_value (rows : Rows n) (rank : Rank n) (height : ℕ) (head : Fin n) :
    (ranksAfterAdd rows rank height head).value =
      Vector.ofFn (SparseRepairGraph.rankAfterAdd (rowValues rows) (rankValues rank) height head) := by
  simp only [ranksAfterAdd, PrimitiveWork.vector_value, ClosureWork.closure_value,
    SparseRepairGraph.rankAfterAdd, SparseClosure.lookup, rankValues]
  rfl

theorem ranksAfterAdd_work_le (rows : Rows n) (rank : Rank n) (height : ℕ) (head : Fin n)
    (rowWork rankWork : ℕ) (hrows : ∀ u v, (rows u v).work ≤ rowWork)
    (hrank : ∀ u, (rank u).work ≤ rankWork) :
    (ranksAfterAdd rows rank height head).work ≤
      ClosureWork.workBound n rowWork + n * (rankWork + 6) := by
  have hc := ClosureWork.closure_work_le rows rowWork hrows
  have hv := PrimitiveWork.vector_work_le (fun v : Fin n =>
    let old := rank v
    (⟨old.value + if (ClosureWork.closure rows).value[head][v] = true then height else 0,
      old.work + 4⟩ : Result ℕ)) (rankWork + 4)
    (fun v => Nat.add_le_add_right (hrank v) 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hv
  exact Nat.add_le_add hc hv

end SortingAdversary.Optimal.LongestPathWork
