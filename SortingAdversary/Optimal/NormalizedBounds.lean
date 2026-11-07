import SortingAdversary.Optimal.PassiveLocalState
import SortingAdversary.Optimal.PublicOrder

/-!
# Structural certificates computed from the maintained state

Topological ranks and their compression are computed by the materialized path
table. One physical comparison produces a graph of at most doubled height
and one additional neighbour. These are the actual inputs of the repair loop
and of the local dynamic-programming oracle.
-/

namespace SortingAdversary.Optimal.NormalizedBounds

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState ControllerRouting Safety
open GraphBalls SparseRepairGraph LocalOracle PassiveLocalState

variable {n : ℕ}

def publicRank (s : State n) : Fin n → ℕ :=
  let ranks := Vector.ofFn (fun x => (PublicOrder.extensionRank s.pool.system.edge x).val)
  fun x => ranks[x]

@[simp] theorem publicRank_eq (s : State n) (x : Fin n) :
    publicRank s x = (PublicOrder.extensionRank s.pool.system.edge x).val := by simp [publicRank]

theorem publicRank_strict (s : State n) (x y : Fin n) (hxy : Arc s.rows.active x y) :
    publicRank s x < publicRank s y := by
  simp only [publicRank_eq]
  exact PublicOrder.extensionRank_strict
    ⟨s.pool.invariant.closed.refl, s.pool.invariant.closed.trans, s.pool.invariant.antisymm⟩
    (s.rows.active_public hxy.2) hxy.1

theorem publicRank_bound (s : State n) (x : Fin n) : publicRank s x < n := by
  rw [publicRank_eq]
  exact (PublicOrder.extensionRank s.pool.system.edge x).isLt

def rank (s : State n) : Fin n → ℕ := heightRank s.rows.active (publicRank s) n

theorem rank_strict (s : State n) (x y : Fin n) (hxy : Arc s.rows.active x y) : rank s x < rank s y :=
  heightRank_strict s.rows.active (publicRank s) n (publicRank_strict s) (publicRank_bound s) hxy

theorem rank_height (s : State n) (H : ℕ)
    (hh : ∀ path : List (Fin n), path.IsChain (fun x y => Arc s.rows.active y x) → path.length < H)
    (x : Fin n) : rank s x + 1 < H := by
  have hl := hh _ (longestChain_chain s.rows.active (publicRank s) n
    (publicRank_strict s) (publicRank_bound s))
  exact (heightRank_bound s.rows.active (publicRank s) n (publicRank_strict s)
    (publicRank_bound s) x).trans_lt hl

def readyBounds {p : ScaleParameters} {D H : ℕ} {q : Pool n} {d : LocalData q}
    (ready : Ready p D H q d) (H' d' : ℕ) (hH : H ≤ H') (hd : D ≤ d') :
    SparseBounds d.rows H' d' where
  rank := rank (state q d)
  strict := rank_strict (state q d)
  height x := (rank_height (state q d) H ready.paths x).le.trans hH
  degree x := (ready.degree x).le.trans hd

def added (q : Pool n) (d : LocalData q) (a b : Fin n)
    (ha : a ∈ q.members) (hb : b ∈ q.members) (hne : a ≠ b)
    (hi : Invariant (closedAdd q.system a b) q.pins) : State n :=
  state (PoolTree.Tree.addComparison q a b ha hb hi) (d.add q a b ha hb hne hi)

theorem added_active_subset (q : Pool n) (d : LocalData q) (a b : Fin n)
    (ha : a ∈ q.members) (hb : b ∈ q.members) (hne : a ≠ b)
    (hi : Invariant (closedAdd q.system a b) q.pins) (x y : Fin n)
    (hxy : (added q d a b ha hb hne hi).rows.active x y = true) :
    addRow d.rows.active a b x y = true := by
  change (d.rows.active x y || decide (x = a ∧ y = b ∧ q.pins a = none ∧ q.pins b = none)) = true at hxy
  have hh : d.rows.active x y = true ∨
      (x = a ∧ y = b ∧ q.pins a = none ∧ q.pins b = none) := by simpa using hxy
  rcases hh with hold | hnew
  · exact (addRow_true _ _ _ _ _).mpr (Or.inl hold)
  · exact (addRow_true _ _ _ _ _).mpr (Or.inr ⟨hnew.1, hnew.2.1⟩)

theorem no_active_back (q : Pool n) (d : LocalData q) (a b : Fin n)
    (hba : q.system.edge b a ≠ true) : SparseClosure.closure d.rows.active b a = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hba (NumericalRepresentation.closure_subset_closed d.rows.active q.system.edge
    q.invariant.closed.refl q.invariant.closed.trans
    (fun _ _ hh => d.rows.active_public hh) b a h)

/-- The new rank reads a materialized reachability table and the already
compressed old ranks. It never searches for a topological ordering by choice. -/
def afterComparisonBounds {p : ScaleParameters} {D H : ℕ} {q : Pool n} {d : LocalData q}
    (ready : Ready p D H q d) (a b : Fin n)
    (ha : a ∈ q.members) (hb : b ∈ q.members) (hne : a ≠ b)
    (hi : Invariant (closedAdd q.system a b) q.pins) (hba : q.system.edge b a ≠ true)
    (H' d' : ℕ) (hH : 2 * H ≤ H') (hd : D + 1 ≤ d') :
    SparseBounds (added q d a b ha hb hne hi).rows H' d' where
  rank := rankAfterAdd d.rows.active (rank (state q d)) H b
  strict x y hxy := rankAfterAdd_strict d.rows.active (rank (state q d)) H
    (rank_strict (state q d)) (fun x => by have := rank_height (state q d) H ready.paths x; omega)
    a b (no_active_back q d a b hba) x y
    ⟨hxy.1, added_active_subset q d a b ha hb hne hi x y hxy.2⟩
  height x := (rankAfterAdd_bound d.rows.active (rank (state q d)) H
    (fun x => by have := rank_height (state q d) H ready.paths x; omega) b x).trans_le hH
  degree x := (degree_mono _ _ (added_active_subset q d a b ha hb hne hi) x).trans
    ((addRow_degree_le d.rows.active a b D (fun x => (ready.degree x).le) x).trans hd)

/-- Both numerical comparison estimates are actual local DP calls. Their
full-parent approximation error follows from the maintained width tests. -/
def estimates {p : ScaleParameters} {D H : ℕ} {q : Pool n} {d : LocalData q}
    (ready : Ready p D H q d) (d' : ℕ) (hH : H ≤ p.H) (hd : D ≤ d')
    (ε : ℚ) (hε : 0 < ε)
    (hminimum : LocalParameters.minimumWidth p.H (LocalAccuracy.influenceSize p.H d') p.R ε ≤ p.width.W₀)
    (a b : Fin n) (hne : a ≠ b) : PoolTree.Tree.Estimates q a b ε where
  forward := qBranch d.rows p.H d' p.R ε a b
  reverse := qBranch d.rows p.H d' p.R ε b a
  forward_error := qBranch_accuracy d.rows q.pin_bounds q.count_pos p.H d'
    (readyBounds ready p.H d' hH hd) p.R ε (by positivity) hε a b hne.symm
    (ready.widths.markCondition d' ε hminimum a) (ready.widths.markCondition d' ε hminimum b)
  reverse_error := qBranch_accuracy d.rows q.pin_bounds q.count_pos p.H d'
    (readyBounds ready p.H d' hH hd) p.R ε (by positivity) hε b a hne
    (ready.widths.markCondition d' ε hminimum b) (ready.widths.markCondition d' ε hminimum a)

end SortingAdversary.Optimal.NormalizedBounds
