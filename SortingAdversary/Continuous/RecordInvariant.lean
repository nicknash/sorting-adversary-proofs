import SortingAdversary.Continuous.ControllerInvariant
import SortingAdversary.Continuous.TraceGuarantees

/-!
# Recording an answer preserves positive volume and the temporary graph bounds

The actual routed event retains its certified volume fraction. Its arc or
bound update is then normalized using the computed graph order. Positive
volume excludes a backward path for a newly inserted arc, giving the exact
one-arc degree and height bounds required throughout repair.
-/

namespace SortingAdversary.Continuous.Controller

open FiniteAveraging OrderRegion TreeState MeasureTheory OneArcRepair
open SortingAdversary.Optimal.GraphBalls
open SortingAdversary.Optimal.SparseClosure
open SortingAdversary.Optimal.SparseRepairGraph

variable {n k : ℕ}

def answerOrder (M : Memory n) (q : Query n) (a : Answer) : List (Fin n) :=
  rankOrder (GraphOrder.graphRank (record M.tree q a).system)

def recorded (M : Memory n) (q : Query n) (a : Answer) : Memory n :=
  applyAction M (.answer q a (answerOrder M q a))

@[simp] theorem recorded_history (M : Memory n) (q : Query n) (a : Answer) :
    (recorded M q a).history = ⟨q, a⟩ :: M.history := rfl

theorem recorded_toReal (M : Memory n) (q : Query n) (a : Answer) :
    (recorded M q a).tree.toReal =
      TreeState.normalize (record M.tree.toReal q a) (answerOrder M q a) := by
  simp only [recorded, applyAction, normalize_toReal, record_toReal]

theorem recorded_edge (M : Memory n) (q : Query n) (a : Answer) :
    (recorded M q a).tree.system.edge = (record M.tree q a).system.edge := by
  simp only [recorded, applyAction, TreeState.normalize, OrderRegion.normalize_edge]

theorem Geometric.recorded {M : Memory n} (h : Geometric M) (hk : 64 ≤ k)
    (q : Query n) (a : Answer)
    (hr : (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).AnchorAnswer a)
    (hp : answerRetained k ≤ (uniformMeasure M.tree.system.toReal).real
      {X | (route (M.tree.toReal.location q.left) (M.tree.toReal.location q.right)).Holds
        (X q.left) (X q.right) a}) : Geometric (Controller.recorded M q a) := by
  let s := record M.tree.toReal q a
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hretained : 0 < answerRetained k := by linarith [(answerRetained_bounds hkR).1]
  have hret := record_volume_retention M.tree.toReal q a hr
    (nodeVolume_pos _ h.positive) (answerRetained k) hp
  have hV : 0 < nodeVolume s.system :=
    (mul_pos hretained (nodeVolume_pos _ h.positive)).trans_le hret
  have hV' : 0 < volume (region s.system) := (ENNReal.toReal_pos_iff.mp hV).1
  obtain ⟨r, hrbound, hrank⟩ := rank_of_positive s.system hV'
  have hedge : (record M.tree q a).system.edge = s.system.edge := by
    exact congrArg (fun st : State n ℝ => st.system.edge) (record_toReal M.tree q a)
  have hnorm : Normalized (OrderRegion.normalize s.system (answerOrder M q a)) := by
    unfold answerOrder
    apply normalize_rankOrder_normalized
    have hg := GraphOrder.graphRank_strict (record M.tree q a).system r
      (fun x y hxy => hrank x y (by rw [← hedge]; exact hxy))
    intro x y hxy
    exact hg x y (by rw [hedge]; exact hxy)
  constructor
  · change 0 < volume (region (Controller.recorded M q a).tree.toReal.system)
    rw [recorded_toReal]
    simpa only [TreeState.normalize, normalize_region] using hV'
  · change Normalized (Controller.recorded M q a).tree.toReal.system
    rw [recorded_toReal]
    exact hnorm
  · rw [recorded_toReal]
    exact normalize_unitBounds s (record_unitBounds M.tree.toReal h.bounds q a) _
  · rw [recorded_toReal]
    exact normalize_localArcs s (record_localArcs M.tree.toReal h.localArcs q a) _
  · rw [recorded_history, recorded_toReal]
    exact normalize_consistent s _ (record_consistent M.tree.toReal M.history h.consistent q a hr) _

/-- Recording either changes no arcs or inserts the one oriented query arc. -/
theorem record_edge_cases (M : Memory n) (q : Query n) (a : Answer) :
    (recorded M q a).tree.system.edge = M.tree.system.edge ∨
    (recorded M q a).tree.system.edge = SortingAdversary.Optimal.SparseRepairGraph.addRow M.tree.system.edge q.left q.right ∨
    (recorded M q a).tree.system.edge = SortingAdversary.Optimal.SparseRepairGraph.addRow M.tree.system.edge q.right q.left := by
  simp only [recorded_edge]
  cases hr : route (M.tree.location q.left) (M.tree.location q.right) with
  | coordinates =>
    cases a with
    | less =>
      apply Or.inr ∘ Or.inl
      simp only [record, hr, recordSystem]
      rfl
    | greater =>
      apply Or.inr ∘ Or.inr
      simp only [record, hr, recordSystem]
      rfl
  | leftFree c => cases a <;> exact Or.inl (by simp [record, hr, recordSystem, boundBelow, boundAbove])
  | rightFree c => cases a <;> exact Or.inl (by simp [record, hr, recordSystem, boundBelow, boundAbove])
  | anchors c d => cases a <;> exact Or.inl (by simp [record, hr, recordSystem])

theorem addRow_back_false (D D' : System (Fin n) ℝ) (u v : Fin n)
    (hV : 0 < volume (region D')) (he : D'.edge = SortingAdversary.Optimal.SparseRepairGraph.addRow D.edge u v) :
    closure D.edge v u = false := by
  obtain ⟨X, hX⟩ := (volume_pos_iff_nonempty D').mp hV
  have hold : SortingAdversary.Optimal.SparseClosure.Respects D.edge X := by
    intro x y hxy
    exact (hX.2 x y (by rw [he]; simp [SortingAdversary.Optimal.SparseRepairGraph.addRow, hxy])).le
  have hclosure := (respects_closure D.edge X).mpr hold
  have huv : X u < X v := hX.2 u v (by rw [he]; simp [SortingAdversary.Optimal.SparseRepairGraph.addRow])
  apply Bool.eq_false_iff.mpr
  intro hback
  exact (not_lt_of_ge (hclosure v u hback)) huv

theorem Ready.recordedAdmissible {M : Memory n} (h : Ready k M)
    (q : Query n) (a : Answer) (hnew : Geometric (recorded M q a)) :
    Admissible k (recorded M q a) := by
  obtain ⟨r, hrank, hrbound⟩ := short_rank_of_height M.tree.system.toReal h.positive
    (2 ^ k) h.height
  have caseAdd (u v : Fin n)
      (he : (recorded M q a).tree.system.edge = SortingAdversary.Optimal.SparseRepairGraph.addRow M.tree.system.edge u v) :
      Admissible k (recorded M q a) := by
    refine ⟨hnew, ?_, ?_⟩
    · rw [he]
      exact addRow_degree_le_threshold _ u v k h.degree
    · intro p hp
      have hback := addRow_back_false M.tree.system.toReal
        (recorded M q a).tree.system.toReal u v hnew.positive he
      have hrank' : ∀ x y, Arc M.tree.system.edge x y → r x < r y := fun x y hxy => hrank x y hxy.2
      have hp' : p.reverse.IsChain (fun x y => Arc (SortingAdversary.Optimal.SparseRepairGraph.addRow M.tree.system.edge u v) y x) := by
        rw [he] at hp
        simpa only [OneArcRepair.Path, List.isChain_reverse] using hp
      have hh := addRow_height_lt M.tree.system.edge r (2 ^ k) hrank' hrbound u v hback hp'
      simpa only [List.length_reverse, ArbitraryLabels.pathHeight, pow_succ, Nat.mul_comm] using hh
  rcases record_edge_cases M q a with he | he | he
  · refine ⟨hnew, ?_, ?_⟩
    · rw [he]
      exact h.admissible.degree
    · rw [he]
      exact h.admissible.height
  · exact caseAdd q.left q.right he
  · exact caseAdd q.right q.left he

end SortingAdversary.Continuous.Controller
