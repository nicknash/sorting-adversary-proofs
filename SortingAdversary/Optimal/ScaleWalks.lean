import SortingAdversary.Optimal.ScaleGeometry

/-!
# Executable breadth layers and shortest scale-repair walks

Each breadth layer is stored as a finite vector. Distance is selected from
the bounded list of radii `0,...,n`, and reconstruction chooses the least
qualifying original label at each step. All mathematical existence arguments
are proofs; neither `Classical.choose` nor unbounded search enters the code.
-/

namespace SortingAdversary.Optimal.ScaleWalks

open GraphBalls ScaleGeometry

variable {n : ℕ}

/-- Simultaneous materialized breadth expansion from every possible center.
The previous layer is computed once before any next-layer entry is formed. -/
def reachTable (E : Fin n → Fin n → Bool) : ℕ → Vector (Finset (Fin n)) n
  | 0 => Vector.ofFn (fun x => {x})
  | r + 1 =>
    let old := reachTable E r
    Vector.ofFn (fun x => (closedNeighbors E x).biUnion (fun y => old[y]))

@[simp] theorem reachTable_get (E : Fin n → Fin n → Bool) (r : ℕ) (x : Fin n) :
    (reachTable E r)[x] = ball E x r := by
  induction r generalizing x with
  | zero => simp [reachTable]
  | succ r ih => simp [reachTable, ball, ih]

/-- Reading a walk from its final step rather than its first step. -/
theorem mem_ball_succ_last (E : Fin n → Fin n → Bool) (x y : Fin n) (r : ℕ) :
    y ∈ ball E x (r + 1) ↔ ∃ u ∈ ball E x r, y ∈ closedNeighbors E u := by
  constructor
  · intro h
    obtain ⟨u, hu, hx⟩ := (mem_ball_succ E y x r).mp (ball_symm E h)
    exact ⟨u, ball_symm E hx, (closedNeighbors_symm E y u).mp hu⟩
  · rintro ⟨u, hu, hy⟩
    exact mem_ball_add E hu ((mem_ball_one E u y).mpr hy)

/-- A saturated breadth layer contains every finite reachable vertex. -/
theorem ball_stable (E : Fin n → Fin n → Bool) (x : Fin n) (r : ℕ)
    (hstable : ball E x (r + 1) ⊆ ball E x r) : ∀ t, ball E x t ⊆ ball E x r := by
  intro t
  induction t with
  | zero =>
    intro y hy
    have hy' : y = x := by simpa only [ball_zero, Finset.mem_singleton] using hy
    subst y
    exact center_mem_ball E x r
  | succ t ih =>
    intro y hy
    obtain ⟨u, hu, hyu⟩ := (mem_ball_succ_last E x y t).mp hy
    exact hstable ((mem_ball_succ_last E x y r).mpr ⟨u, ih hu, hyu⟩)

/-- Finite breadth expansion reaches every connected label by radius `n`.
Otherwise each of its first `n` expansions strictly increases cardinality. -/
theorem connected_mem_ball (E : Fin n → Fin n → Bool) (x y : Fin n)
    (hconn : Connected E x y) : y ∈ ball E x n := by
  by_contra hmissing
  have hstrict (r : ℕ) (hr : r < n) : ball E x r ⊂ ball E x (r + 1) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨ball_step E x r, ?_⟩
    intro heq
    obtain ⟨t, hy⟩ := hconn
    have hsat := ball_stable E x r (by rw [heq]) t hy
    exact hmissing (ball_mono E x hr.le hsat)
  have hgrowth : ∀ r, r ≤ n → r + 1 ≤ (ball E x r).card := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih =>
      intro hr
      have hprev := ih (by omega : r ≤ n)
      have hcard := Finset.card_lt_card (hstrict r (by omega))
      omega
  have hbig := hgrowth n le_rfl
  have hsmall : (ball E x n).card ≤ n := by simpa using Finset.card_le_univ (ball E x n)
  omega

theorem connected_iff_mem_ball (E : Fin n → Fin n → Bool) (x y : Fin n) :
    Connected E x y ↔ y ∈ ball E x n :=
  ⟨connected_mem_ball E x y, fun h => ⟨n, h⟩⟩

/-- A computable connectivity test on the materialized radius-`n` layer. -/
def connected (E : Fin n → Fin n → Bool) (x y : Fin n) : Bool :=
  decide (y ∈ (reachTable E n)[x])

@[simp] theorem connected_eq_true (E : Fin n → Fin n → Bool) (x y : Fin n) :
    connected E x y = true ↔ Connected E x y := by
  simp only [connected, decide_eq_true_eq, reachTable_get, connected_iff_mem_ball]

/-- Candidate next labels for a walk with `r+1` remaining edges. -/
def candidates (E : Fin n → Fin n → Bool) (x y : Fin n) (r : ℕ) : Finset (Fin n) :=
  let old := reachTable E r
  (closedNeighbors E x).filter (fun u => y ∈ old[u])

@[simp] theorem mem_candidates (E : Fin n → Fin n → Bool) (x y u : Fin n) (r : ℕ) :
    u ∈ candidates E x y r ↔ u ∈ closedNeighbors E x ∧ y ∈ ball E u r := by
  simp only [candidates, Finset.mem_filter, reachTable_get]

theorem candidates_nonempty (E : Fin n → Fin n → Bool) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball E x (r + 1)) : (candidates E x y r).Nonempty := by
  obtain ⟨u, hu, hy⟩ := (mem_ball_succ E x y r).mp h
  exact ⟨u, (mem_candidates E x y u r).mpr ⟨hu, hy⟩⟩

/-- Original numeric label order gives a fixed deterministic tie break. -/
def nextLabel (E : Fin n → Fin n → Bool) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball E x (r + 1)) : Fin n :=
  (candidates E x y r).min' (candidates_nonempty E x y r h)

theorem nextLabel_spec (E : Fin n → Fin n → Bool) (x y : Fin n) (r : ℕ)
    (h : y ∈ ball E x (r + 1)) :
    nextLabel E x y r h ∈ closedNeighbors E x ∧ y ∈ ball E (nextLabel E x y r h) r :=
  (mem_candidates E x y _ r).mp (Finset.min'_mem _ _)

/-- Construct the actual walk from the stored breadth information. -/
def buildWalk (E : Fin n → Fin n → Bool) (x y : Fin n) :
    (r : ℕ) → y ∈ ball E x r → {p : Walk E r // p.start = x ∧ p.finish = y}
  | 0, h => ⟨Walk.single E x, rfl, by
      have hy : y = x := by simpa only [ball_zero, Finset.mem_singleton] using h
      exact hy.symm⟩
  | r + 1, h =>
    let u := nextLabel E x y r h
    have hu := nextLabel_spec E x y r h
    let p := buildWalk E u y r hu.2
    ⟨p.val.prepend x (by rw [p.property.1]; exact hu.1), rfl, p.property.2⟩

/-- Every candidate radius is explicitly bounded by the finite carrier size. -/
def distanceCandidates (E : Fin n → Fin n → Bool) (x y : Fin n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun r => y ∈ (reachTable E r.val)[x])

@[simp] theorem mem_distanceCandidates (E : Fin n → Fin n → Bool) (x y : Fin n)
    (r : Fin (n + 1)) : r ∈ distanceCandidates E x y ↔ y ∈ ball E x r.val := by
  simp only [distanceCandidates, Finset.mem_filter, Finset.mem_univ, true_and, reachTable_get]

theorem distanceCandidates_nonempty (E : Fin n → Fin n → Bool) (x y : Fin n)
    (hconn : Connected E x y) : (distanceCandidates E x y).Nonempty :=
  ⟨Fin.last n, (mem_distanceCandidates E x y _).mpr (connected_mem_ball E x y hconn)⟩

def distance (E : Fin n → Fin n → Bool) (x y : Fin n) (hconn : Connected E x y) : Fin (n + 1) :=
  (distanceCandidates E x y).min' (distanceCandidates_nonempty E x y hconn)

theorem distance_reaches (E : Fin n → Fin n → Bool) (x y : Fin n) (hconn : Connected E x y) :
    y ∈ ball E x (distance E x y hconn).val :=
  (mem_distanceCandidates E x y _).mp (Finset.min'_mem _ _)

theorem distance_minimal (E : Fin n → Fin n → Bool) (x y : Fin n) (hconn : Connected E x y)
    (r : ℕ) (hr : y ∈ ball E x r) : (distance E x y hconn).val ≤ r := by
  by_cases hcap : r ≤ n
  · exact Finset.min'_le _ ⟨r, by omega⟩ ((mem_distanceCandidates E x y _).mpr hr)
  · have hbound := (distance E x y hconn).isLt
    omega

/-- The executable output carries its actual endpoints and shortestness. -/
structure ShortestPath (E : Fin n → Fin n → Bool) (x y : Fin n) where
  length : ℕ
  walk : Walk E length
  start : walk.start = x
  finish : walk.finish = y
  shortest : ∀ r, y ∈ ball E x r → length ≤ r
  length_bound : length ≤ n

def shortestPath (E : Fin n → Fin n → Bool) (x y : Fin n) (hconn : Connected E x y) :
    ShortestPath E x y :=
  let r := distance E x y hconn
  let p := buildWalk E x y r.val (distance_reaches E x y hconn)
  { length := r.val
    walk := p.val
    start := p.property.1
    finish := p.property.2
    shortest := distance_minimal E x y hconn
    length_bound := Nat.le_of_lt_succ r.isLt }

/-- Total executable interface for callers which first test connectivity. -/
def shortestPath? (E : Fin n → Fin n → Bool) (x y : Fin n) : Option (ShortestPath E x y) :=
  if h : connected E x y = true then some (shortestPath E x y ((connected_eq_true E x y).mp h))
  else none

theorem shortestPath?_isSome (E : Fin n → Fin n → Bool) (x y : Fin n) :
    (shortestPath? E x y).isSome = true ↔ Connected E x y := by
  unfold shortestPath?
  split_ifs with h
  · simp only [Option.isSome_some, true_iff]
    exact (connected_eq_true E x y).mp h
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hc => h ((connected_eq_true E x y).mpr hc)

end SortingAdversary.Optimal.ScaleWalks
