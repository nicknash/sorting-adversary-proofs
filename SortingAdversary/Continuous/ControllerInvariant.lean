import SortingAdversary.Continuous.Controller
import SortingAdversary.Continuous.FeasibleRank
import SortingAdversary.Continuous.StateInvariants

/-!
# The geometric and sparse-graph invariants of the executable controller

Positive volume, canonical bounds, locality of arcs, and transcript
consistency concern the actual real interpretation of the rational memory.
Strict rank witnesses are derived from positive volume and graph height;
they are not stored executable inputs.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState MeasureTheory
open OneArcRepair
open SortingAdversary.Optimal.GraphBalls

variable {n k : ℕ}

structure Geometric (M : Memory n) : Prop where
  positive : 0 < volume (region M.tree.system.toReal)
  normalized : Normalized M.tree.system.toReal
  bounds : M.tree.toReal.UnitBounds
  localArcs : M.tree.toReal.LocalArcs
  consistent : M.tree.toReal.Consistent M.history

structure Ready (k : ℕ) (M : Memory n) : Prop extends Geometric M where
  degree : DegreeBelow M.tree.system.edge k
  height : HeightBelow M.tree.system.edge (2 ^ k)

structure Admissible (k : ℕ) (M : Memory n) : Prop extends Geometric M where
  degree : ∀ x, (neighbors M.tree.system.edge x).card ≤ k
  height : HeightBelow M.tree.system.edge (ArbitraryLabels.pathHeight k)

theorem Geometric.noLoop {M : Memory n} (h : Geometric M) :
    ∀ x, M.tree.system.edge x x = false := no_loop_of_positive M.tree.system.toReal h.positive

theorem Geometric.widths {M : Memory n} (h : Geometric M) :
    ∀ x, M.tree.system.lower x < M.tree.system.upper x := by
  intro x
  exact (Rat.cast_lt (K := ℝ)).mp (widths_of_positive M.tree.system.toReal h.positive x)

theorem Geometric.rationalBounds {M : Memory n} (h : Geometric M) :
    ∀ x, 0 ≤ M.tree.system.lower x ∧ M.tree.system.upper x ≤ 1 := by
  intro x
  have hb := h.bounds x
  change (0 : ℝ) ≤ (M.tree.system.lower x : ℝ) ∧
    (M.tree.system.upper x : ℝ) ≤ 1 at hb
  exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩

theorem Ready.admissible {M : Memory n} (h : Ready k M) : Admissible k M := by
  refine ⟨h.toGeometric, fun x => (h.degree x).le, ?_⟩
  intro p hp
  apply (h.height p hp).trans_le
  unfold ArbitraryLabels.pathHeight
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem Admissible.rank {M : Memory n} (h : Admissible k M) :
    ∃ rank : Fin n → ℕ,
      (∀ x y, M.tree.system.edge x y = true → rank x < rank y) ∧
      ∀ x, rank x + 1 ≤ ArbitraryLabels.pathHeight k := by
  obtain ⟨rank, hrank, hh⟩ := short_rank_of_height M.tree.system.toReal h.positive
    (ArbitraryLabels.pathHeight k) h.height
  exact ⟨rank, hrank, fun x => (hh x).le⟩

theorem initial_geometric (n : ℕ) : Geometric (initial n) := by
  constructor
  · apply (volume_pos_iff_nonempty _).mpr
    refine ⟨fun _ => 1 / 2, ?_⟩
    constructor
    · intro x
      norm_num [initial, TreeState.initial, System.toReal]
    · intro x y hxy
      simp [initial, TreeState.initial, System.toReal] at hxy
  · intro x y hxy
    simp [initial, TreeState.initial, System.toReal] at hxy
  · simpa only [initial, TreeState.initial_toReal] using (initial_unitBounds (n := n))
  · exact initial_localArcs
  · simpa only [initial, TreeState.initial_toReal] using (initial_consistent (n := n) (K := ℝ))

theorem initial_ready (n k : ℕ) (hk : 1 ≤ k) : Ready k (initial n) := by
  refine ⟨initial_geometric n, ?_, ?_⟩
  · intro x
    simpa [initial, TreeState.initial, neighbors] using (show 0 < k by omega)
  · intro p hp
    have hlen : p.length ≤ 1 := by
      cases p with
      | nil => simp
      | cons x xs =>
        cases xs with
        | nil => simp
        | cons y ys =>
          have hxy := (List.isChain_cons_cons.mp hp).1.2
          simp [initial, TreeState.initial] at hxy
    have htwo : 1 < 2 ^ k := one_lt_pow₀ (by decide) (by omega)
    exact hlen.trans_lt htwo

/-- Any interior rational move, followed by its computed topological
normalization, preserves the genuine geometric state invariants. -/
theorem Geometric.applyMove {M : Memory n} (h : Geometric M) (m : TraceAccounting.Move n)
    (hc : M.tree.system.lower m.item < m.anchor.coordinate ∧
      m.anchor.coordinate < M.tree.system.upper m.item)
    (ho : m.order = rankOrder (GraphOrder.graphRank
      (resetCoordinate M.tree.system m.item m.anchor.coordinate))) :
    Geometric (Controller.applyMove M m) := by
  let s := refineAt M.tree.toReal m.item (m.anchor.coordinate : ℝ)
  have hcR : M.tree.system.toReal.lower m.item < (m.anchor.coordinate : ℝ) ∧
      (m.anchor.coordinate : ℝ) < M.tree.system.toReal.upper m.item :=
    ⟨(Rat.cast_lt (K := ℝ)).mpr hc.1, (Rat.cast_lt (K := ℝ)).mpr hc.2⟩
  obtain ⟨r, hrbound, hr⟩ := rank_of_positive M.tree.system.toReal h.positive
  let rf (x : Fin n) : Fin n := ⟨r x, hrbound x⟩
  have hV : 0 < nodeVolume s.system :=
    refineAt_volume_pos M.tree.toReal m.item (m.anchor.coordinate : ℝ) h.normalized
      (widths_of_positive M.tree.system.toReal h.positive) rf hr hcR
  have hp : 0 < volume (region s.system) := (ENNReal.toReal_pos_iff.mp hV).1
  obtain ⟨r', hrbound', hr'⟩ := rank_of_positive s.system hp
  have hnorm : Normalized (OrderRegion.normalize s.system m.order) := by
    rw [ho]
    exact normalize_rankOrder_normalized s.system
      (GraphOrder.graphRank (resetCoordinate M.tree.system m.item m.anchor.coordinate))
      (GraphOrder.graphRank_strict _ r' hr')
  have htree : (Controller.applyMove M m).tree.toReal = TreeState.normalize s m.order := by
    simp only [Controller.applyMove, TreeState.normalize_toReal, TreeState.refineAt_toReal]
    rfl
  constructor
  · change 0 < volume (region (Controller.applyMove M m).tree.toReal.system)
    rw [htree]
    simpa only [TreeState.normalize, normalize_region] using hp
  · change Normalized (Controller.applyMove M m).tree.toReal.system
    rw [htree]
    exact hnorm
  · rw [htree]
    exact normalize_unitBounds s (refineAt_unitBounds M.tree.toReal h.bounds _ _) m.order
  · rw [htree]
    exact normalize_localArcs s (refineAt_localArcs M.tree.toReal h.localArcs _ _) m.order
  · change (Controller.applyMove M m).tree.toReal.Consistent M.history
    rw [htree]
    exact normalize_consistent s M.history
      (refineAt_consistent M.tree.toReal M.history h.consistent _ _ (h.noLoop _) hcR) m.order

theorem applyMove_edge (M : Memory n) (m : TraceAccounting.Move n) :
    (Controller.applyMove M m).tree.system.edge =
      SortingAdversary.Optimal.SparseRepairGraph.eraseVertex M.tree.system.edge m.item := by
  simp only [Controller.applyMove, TreeState.normalize, OrderRegion.normalize_edge, refineAt,
    OneArcRepair.resetCoordinate_edge]

theorem applyMove_edge_old (M : Memory n) (m : TraceAccounting.Move n) :
    ∀ x y, (Controller.applyMove M m).tree.system.edge x y = true → M.tree.system.edge x y = true := by
  rw [applyMove_edge]
  exact SortingAdversary.Optimal.SparseRepairGraph.eraseVertex_old _ _

theorem Ready.applyMove {M : Memory n} (h : Ready k M) (m : TraceAccounting.Move n)
    (hc : M.tree.system.lower m.item < m.anchor.coordinate ∧
      m.anchor.coordinate < M.tree.system.upper m.item)
    (ho : m.order = rankOrder (GraphOrder.graphRank
      (resetCoordinate M.tree.system m.item m.anchor.coordinate))) :
    Ready k (Controller.applyMove M m) := by
  exact ⟨h.toGeometric.applyMove m hc ho,
    degreeBelow_mono _ _ k (applyMove_edge_old M m) h.degree,
    heightBelow_mono _ _ (2 ^ k) (applyMove_edge_old M m) h.height⟩

theorem Admissible.applyMove {M : Memory n} (h : Admissible k M)
    (m : TraceAccounting.Move n)
    (hc : M.tree.system.lower m.item < m.anchor.coordinate ∧
      m.anchor.coordinate < M.tree.system.upper m.item)
    (ho : m.order = rankOrder (GraphOrder.graphRank
      (resetCoordinate M.tree.system m.item m.anchor.coordinate))) :
    Admissible k (Controller.applyMove M m) := by
  refine ⟨h.toGeometric.applyMove m hc ho, ?_,
    heightBelow_mono _ _ _ (applyMove_edge_old M m) h.height⟩
  intro x
  exact (SortingAdversary.Optimal.SparseRepairGraph.degree_mono _ _
    (applyMove_edge_old M m) x).trans (h.degree x)

end SortingAdversary.Continuous.Controller
