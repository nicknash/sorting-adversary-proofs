import SortingAdversary.Continuous.TreeState
import SortingAdversary.Continuous.Normalization
import SortingAdversary.Continuous.RefinementBatch
import SortingAdversary.Continuous.GraphPaths
import SortingAdversary.Optimal.SparseRepairGraph

/-!
# One inserted arc and sparse graph repair

If the previous graph has height below `H`, every new path of `H` vertices
uses the inserted arc. Removing its vertices therefore removes an endpoint
of that arc. Similarly, a vertex newly reaching degree `k` is an endpoint of
the inserted arc. In either case the repaired graph is a subgraph of the old
graph, so both strict invariants are restored at once.
-/

namespace SortingAdversary.Continuous.OneArcRepair

open FiniteAveraging OrderRegion TreeState
open SortingAdversary.Optimal.GraphBalls
open SortingAdversary.Optimal.SparseRepairGraph

variable {n : ℕ}

def Path (E : Fin n → Fin n → Bool) (p : List (Fin n)) : Prop :=
  p.IsChain (Arc E)

def HeightBelow (E : Fin n → Fin n → Bool) (H : ℕ) : Prop :=
  ∀ p, Path E p → p.length < H

def DegreeBelow (E : Fin n → Fin n → Bool) (k : ℕ) : Prop :=
  ∀ x, (neighbors E x).card < k

/-- Erase incident arcs while retaining isolated fresh coordinates. -/
def eraseVertices (E : Fin n → Fin n → Bool) (A : Finset (Fin n)) :
    Fin n → Fin n → Bool :=
  fun x y => E x y && decide (x ∉ A ∧ y ∉ A)

@[simp] theorem eraseVertices_true (E : Fin n → Fin n → Bool) (A : Finset (Fin n))
    (x y : Fin n) : eraseVertices E A x y = true ↔ E x y = true ∧ x ∉ A ∧ y ∉ A := by
  simp [eraseVertices]

def eraseList (E : Fin n → Fin n → Bool) (p : List (Fin n)) : Fin n → Fin n → Bool :=
  p.foldl eraseVertex E

theorem eraseList_eq (E : Fin n → Fin n → Bool) (p : List (Fin n)) :
    eraseList E p = eraseVertices E p.toFinset := by
  induction p generalizing E with
  | nil => funext x y; simp [eraseList, eraseVertices]
  | cons v p ih =>
    change eraseList (eraseVertex E v) p = _
    rw [ih]
    funext x y
    simp only [eraseVertices, eraseVertex, List.toFinset_cons, Finset.mem_insert,
      not_or, Bool.and_assoc]
    cases E x y <;> by_cases hx : x = v <;> by_cases hy : y = v <;>
      by_cases hxp : x ∈ p.toFinset <;> by_cases hyp : y ∈ p.toFinset <;>
        simp [hx, hy, hxp, hyp]

theorem resetCoordinate_edge {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (D : System (Fin n) K) (x : Fin n) (c : K) :
    (resetCoordinate D x c).edge = eraseVertex D.edge x := by
  funext u v
  by_cases hu : u = x <;> by_cases hv : v = x <;>
    simp [resetCoordinate, eraseVertex, hu, hv]

theorem heightBelow_mono (E F : Fin n → Fin n → Bool) (H : ℕ)
    (hFE : ∀ x y, F x y = true → E x y = true) (hE : HeightBelow E H) :
    HeightBelow F H := by
  intro p hp
  exact hE p (hp.imp (fun _ _ h => ⟨h.1, hFE _ _ h.2⟩))

theorem degreeBelow_mono (E F : Fin n → Fin n → Bool) (k : ℕ)
    (hFE : ∀ x y, F x y = true → E x y = true) (hE : DegreeBelow E k) :
    DegreeBelow F k := fun x => (degree_mono F E hFE x).trans_lt (hE x)

theorem path_old_of_not_mem_tail (E : Fin n → Fin n → Bool) (u v : Fin n)
    (p : List (Fin n)) (hp : Path (addRow E u v) p) (hu : u ∉ p) : Path E p := by
  apply hp.imp_of_mem_imp
  intro x y hx _ hxy
  refine ⟨hxy.1, ?_⟩
  rcases (addRow_true E u v x y).mp hxy.2 with hold | ⟨rfl, _⟩
  · exact hold
  · exact (hu hx).elim

theorem path_old_of_not_mem_head (E : Fin n → Fin n → Bool) (u v : Fin n)
    (p : List (Fin n)) (hp : Path (addRow E u v) p) (hv : v ∉ p) : Path E p := by
  apply hp.imp_of_mem_imp
  intro x y _ hy hxy
  refine ⟨hxy.1, ?_⟩
  rcases (addRow_true E u v x y).mp hxy.2 with hold | ⟨_, rfl⟩
  · exact hold
  · exact (hv hy).elim

/-- Every path reaching the repair threshold contains both endpoints of
the newly inserted arc. This is derived from the old strict height bound. -/
theorem path_contains_new_endpoints (E : Fin n → Fin n → Bool) (u v : Fin n)
    (H : ℕ) (hE : HeightBelow E H) (p : List (Fin n))
    (hp : Path (addRow E u v) p) (hlen : H ≤ p.length) : u ∈ p ∧ v ∈ p := by
  constructor
  · by_contra hu
    exact (Nat.not_lt_of_ge hlen) (hE p (path_old_of_not_mem_tail E u v p hp hu))
  · by_contra hv
    exact (Nat.not_lt_of_ge hlen) (hE p (path_old_of_not_mem_head E u v p hp hv))

theorem eraseVertices_addRow_le_old (E : Fin n → Fin n → Bool) (u v : Fin n)
    (A : Finset (Fin n)) (hA : u ∈ A ∨ v ∈ A) :
    ∀ x y, eraseVertices (addRow E u v) A x y = true → E x y = true := by
  intro x y hxy
  obtain ⟨he, hx, hy⟩ := (eraseVertices_true _ A x y).mp hxy
  rcases (addRow_true E u v x y).mp he with hold | ⟨rfl, rfl⟩
  · exact hold
  · exact (hA.elim hx hy).elim

theorem path_repair_le_old (E : Fin n → Fin n → Bool) (u v : Fin n)
    (H : ℕ) (hE : HeightBelow E H) (p : List (Fin n))
    (hp : Path (addRow E u v) p) (hlen : H ≤ p.length) :
    ∀ x y, eraseList (addRow E u v) p x y = true → E x y = true := by
  rw [eraseList_eq]
  exact eraseVertices_addRow_le_old E u v p.toFinset
    (Or.inl (List.mem_toFinset.mpr (path_contains_new_endpoints E u v H hE p hp hlen).1))

theorem path_repair_restores (E : Fin n → Fin n → Bool) (u v : Fin n)
    (H k : ℕ) (hheight : HeightBelow E H) (hdegree : DegreeBelow E k)
    (p : List (Fin n)) (hp : Path (addRow E u v) p) (hlen : H ≤ p.length) :
    HeightBelow (eraseList (addRow E u v) p) H ∧
      DegreeBelow (eraseList (addRow E u v) p) k := by
  have hm := path_repair_le_old E u v H hheight p hp hlen
  exact ⟨heightBelow_mono _ _ H hm hheight, degreeBelow_mono _ _ k hm hdegree⟩

theorem addRow_neighbors_of_not_endpoint (E : Fin n → Fin n → Bool)
    (u v x : Fin n) (hxu : x ≠ u) (hxv : x ≠ v) :
    neighbors (addRow E u v) x = neighbors E x := by
  ext y
  simp only [mem_neighbors, addRow_true, hxu, hxv, false_and, and_false,
    or_false]

/-- A degree witness reaching `k` after insertion must be one of the two
inserted endpoints, because all other neighbor sets are unchanged. -/
theorem degree_witness_is_endpoint (E : Fin n → Fin n → Bool) (u v : Fin n)
    (k : ℕ) (hdegree : DegreeBelow E k) (x : Fin n)
    (hx : k ≤ (neighbors (addRow E u v) x).card) : x = u ∨ x = v := by
  by_contra h
  have hxu : x ≠ u := fun hxu => h (Or.inl hxu)
  have hxv : x ≠ v := fun hxv => h (Or.inr hxv)
  rw [addRow_neighbors_of_not_endpoint E u v x hxu hxv] at hx
  exact (Nat.not_lt_of_ge hx) (hdegree x)

theorem degree_repair_le_old (E : Fin n → Fin n → Bool) (u v : Fin n)
    (k : ℕ) (hdegree : DegreeBelow E k) (x : Fin n)
    (hx : k ≤ (neighbors (addRow E u v) x).card) :
    ∀ y z, eraseVertex (addRow E u v) x y z = true → E y z = true := by
  have hends := degree_witness_is_endpoint E u v k hdegree x hx
  have hm := eraseVertices_addRow_le_old E u v {x}
    (hends.elim (fun h => Or.inl (by simp [h])) (fun h => Or.inr (by simp [h])))
  simpa only [eraseVertices, eraseVertex, Finset.mem_singleton] using hm

theorem degree_repair_restores (E : Fin n → Fin n → Bool) (u v : Fin n)
    (H k : ℕ) (hheight : HeightBelow E H) (hdegree : DegreeBelow E k)
    (x : Fin n) (hx : k ≤ (neighbors (addRow E u v) x).card) :
    HeightBelow (eraseVertex (addRow E u v) x) H ∧
      DegreeBelow (eraseVertex (addRow E u v) x) k := by
  have hm := degree_repair_le_old E u v k hdegree x hx
  exact ⟨heightBelow_mono _ _ H hm hheight, degreeBelow_mono _ _ k hm hdegree⟩

/-- The transient graph has degree at most `k`, before either repair. -/
theorem addRow_degree_le_threshold (E : Fin n → Fin n → Bool) (u v : Fin n)
    (k : ℕ) (hdegree : DegreeBelow E k) (x : Fin n) :
    (neighbors (addRow E u v) x).card ≤ k := by
  have hc := (Finset.card_le_card (addRow_neighbors E u v x)).trans
    (Finset.card_insert_le _ _)
  have hx := hdegree x
  omega

theorem path_of_chain (E : Fin n → Fin n → Bool) (hloop : ∀ x, E x x = false)
    {p : List (Fin n)} (hp : p.IsChain (fun x y => E x y = true)) : Path E p := by
  apply hp.imp
  intro x y hxy
  refine ⟨?_, hxy⟩
  intro he
  subst y
  simp [hloop x] at hxy

/-- The executable path search detects exactly failure of the strict
height invariant, including a longer path through its initial `H` vertices. -/
theorem firstPath_none_iff_heightBelow (E : Fin n → Fin n → Bool) (H : ℕ)
    (hloop : ∀ x, E x x = false) :
    GraphPaths.firstPath E H = none ↔ HeightBelow E H := by
  rw [GraphPaths.firstPath_none]
  constructor
  · intro h p hp
    by_contra hlen
    have hge : H ≤ p.length := Nat.le_of_not_gt hlen
    have ht := h (p.take H) ((hp.imp (fun _ _ hxy => hxy.2)).take H)
    exact ht (by simp [List.length_take, Nat.min_eq_left hge])
  · intro h p hp hlen
    have hh := h p (path_of_chain E hloop hp)
    omega

/-- The old dynamic-programming height test and the forward path invariant
agree; its reverse-list implementation does not change the convention here. -/
theorem computed_height_iff (E : Fin n → Fin n → Bool) (rank : Fin n → ℕ)
    (bound H : ℕ) (hrank : ∀ x y, Arc E x y → rank x < rank y)
    (hbound : ∀ x, rank x < bound) :
    height E rank bound < H ↔ HeightBelow E H := by
  rw [height_lt_iff E rank bound H hrank hbound]
  constructor
  · intro h p hp
    have hr : p.reverse.IsChain (fun x y => Arc E y x) := by
      simpa only [Path, List.isChain_reverse] using hp
    simpa only [List.length_reverse] using h p.reverse hr
  · intro h p hp
    have hr : Path E p.reverse := by
      simpa only [Path, List.isChain_reverse] using hp
    simpa only [List.length_reverse] using h p.reverse hr

/-- The graph after a real batch of refinements is exactly the original
graph with every refined coordinate's incident arcs erased. Normalization
changes bounds only, so it introduces no extra graph hypothesis. -/
theorem refinementSteps_edge {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {s s' : TreeState.State n K} {moves : List (Fin n × K)}
    (h : RefinementSteps s moves s') :
    s'.system.edge = eraseList s.system.edge (moves.map Prod.fst) := by
  induction h with
  | nil s => rfl
  | cons s x c order moves s' hxx hc tail ih =>
    calc
      s'.system.edge = eraseList (TreeState.normalize (refineAt s x c) order).system.edge
          (moves.map Prod.fst) := ih
      _ = eraseList (eraseVertex s.system.edge x) (moves.map Prod.fst) := by
        congr 1
        change (OrderRegion.normalize (resetCoordinate s.system x c) order).edge = _
        rw [normalize_edge, resetCoordinate_edge]
      _ = eraseList s.system.edge (((x, c) :: moves).map Prod.fst) := rfl

/-- The lexicographically selected path, followed by the actual refinement
batch, restores both strict sparse-graph invariants. -/
theorem firstPath_refinement_restores {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (E : Fin n → Fin n → Bool) (u v : Fin n)
    (H k : ℕ) (hheight : HeightBelow E H) (hdegree : DegreeBelow E k)
    {s s' : TreeState.State n K} {moves : List (Fin n × K)}
    (hedge : s.system.edge = addRow E u v)
    (hloop : ∀ x, s.system.edge x x = false)
    (hpath : GraphPaths.firstPath s.system.edge H = some (moves.map Prod.fst))
    (hsteps : RefinementSteps s moves s') :
    HeightBelow s'.system.edge H ∧ DegreeBelow s'.system.edge k := by
  obtain ⟨hlen, hp, _⟩ := GraphPaths.firstPath_some s.system.edge H _ hpath
  have hp' := path_of_chain s.system.edge hloop hp
  rw [hedge] at hp'
  rw [refinementSteps_edge hsteps, hedge]
  exact path_repair_restores E u v H k hheight hdegree _ hp' hlen.ge

/-- The same conclusion for a real single-vertex degree repair. -/
theorem degree_refinement_restores {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (E : Fin n → Fin n → Bool) (u v : Fin n)
    (H k : ℕ) (hheight : HeightBelow E H) (hdegree : DegreeBelow E k)
    {s s' : TreeState.State n K} (x : Fin n) (c : K)
    (hedge : s.system.edge = addRow E u v)
    (hx : k ≤ (neighbors s.system.edge x).card)
    (hsteps : RefinementSteps s [(x, c)] s') :
    HeightBelow s'.system.edge H ∧ DegreeBelow s'.system.edge k := by
  rw [hedge] at hx
  rw [refinementSteps_edge hsteps, hedge]
  exact degree_repair_restores E u v H k hheight hdegree x hx

end SortingAdversary.Continuous.OneArcRepair
