import SortingAdversary.Optimal.WidthNormalize
import SortingAdversary.Optimal.ScaleWalks
import SortingAdversary.Optimal.ScalePinPreservation

/-!
# Concrete scale reservations

A materialized breadth table identifies the first connected pair with a
violating width ratio. The actual shortest-path routine and finite first
crossing searches select the reserved labels. Their central insertion
intervals are passed to the chronological, veto-aware hub executor.
-/

namespace SortingAdversary.Optimal.WidthRepair

open WeakMaps WeakMaps.WeakSystem FiniteInsertion NumericalRepresentation SparseClosure
open GraphBalls PoolState ScaleGeometry ScaleHubs ScaleMass StableBatches HubSelector BatchWindows

variable {n : ℕ}

structure ScaleParameters where
  width : WidthParameters
  H : ℕ
  J : ℕ
  group : 4 ≤ J

namespace ScaleParameters

def A (p : ScaleParameters) : ℕ := scaleBase p.J p.width.L p.H
def R (p : ScaleParameters) : ℕ := p.A ^ (p.J + 1)

theorem J_pos (p : ScaleParameters) : 0 < p.J := lt_of_lt_of_le (by decide) p.group
theorem gap (p : ScaleParameters) : p.width.L ^ (2 * p.H + 1) < p.A :=
  scaleBase_gap p.J p.width.L p.H p.J_pos
theorem A_pos (p : ScaleParameters) : 0 < p.A := lt_of_le_of_lt (Nat.zero_le _) p.gap
theorem one_le_A (p : ScaleParameters) : 1 ≤ p.A := p.A_pos
theorem one_le_R (p : ScaleParameters) : 1 ≤ p.R := one_le_pow₀ p.one_le_A
theorem veto_gap (p : ScaleParameters) : 8 * p.J * p.width.L ≤ p.A :=
  scaleBase_veto_gap p.J p.width.L p.H

end ScaleParameters

/-- The connectivity table is computed once for the complete pair scan. -/
def scaleWitness (s : State n) (R : ℕ) : Option (Fin n × Fin n) :=
  let reachable := ScaleWalks.reachTable s.rows.active n
  ((List.finRange n).flatMap (fun x => (List.finRange n).map (fun y => (x, y)))).find?
    (fun xy => decide (xy.2 ∈ reachable[xy.1] ∧ R * s.width xy.1 < s.width xy.2))

theorem scaleWitness_some (s : State n) (R : ℕ) {xy : Fin n × Fin n}
    (h : scaleWitness s R = some xy) :
    Connected s.rows.active xy.1 xy.2 ∧ R * s.width xy.1 < s.width xy.2 := by
  have hs := of_decide_eq_true (List.find?_some
    (p := fun z : Fin n × Fin n => decide (z.2 ∈ (ScaleWalks.reachTable s.rows.active n)[z.1] ∧
      R * s.width z.1 < s.width z.2)) h)
  rw [ScaleWalks.reachTable_get] at hs
  exact ⟨(ScaleWalks.connected_iff_mem_ball _ _ _).mpr hs.1, hs.2⟩

theorem scaleWitness_none (s : State n) (R : ℕ) : scaleWitness s R = none ↔
    ∀ x y, Connected s.rows.active x y → s.width y ≤ R * s.width x := by
  have ht (x : Fin n) : (ScaleWalks.reachTable s.rows.active n)[x.val] = ball s.rows.active x n := by
    simpa only [Fin.getElem_fin] using ScaleWalks.reachTable_get s.rows.active n x
  simp [scaleWitness, List.find?_eq_none, ht, ScaleWalks.connected_iff_mem_ball]

structure ScaleTrigger (s : State n) (p : ScaleParameters) where
  low : Fin n
  high : Fin n
  connected : Connected s.rows.active low high
  steep : p.R * s.width low < s.width high

def selectScale (s : State n) (p : ScaleParameters) : Option (ScaleTrigger s p) :=
  match h : scaleWitness s p.R with
  | none => none
  | some xy => some ⟨xy.1, xy.2, (scaleWitness_some s p.R h).1, (scaleWitness_some s p.R h).2⟩

theorem selectScale_none (s : State n) (p : ScaleParameters) : selectScale s p = none ↔
    ∀ x y, Connected s.rows.active x y → s.width y ≤ p.R * s.width x := by
  unfold selectScale
  split
  · rename_i h
    simp only [true_iff]
    exact (scaleWitness_none s p.R).mp h
  · rename_i xy h
    simp only [Option.some_ne_none, false_iff]
    intro hall
    have hs := scaleWitness_some s p.R h
    exact Nat.not_lt_of_ge (hall xy.1 xy.2 hs.1) hs.2

namespace EarlyNormal

theorem scaleBound {s : State n} {W₀ L : ℕ} (h : EarlyNormal s W₀ L) :
    EdgeScaleBound s.rows.active s.width L := by
  intro x y hy
  obtain ⟨_, hxy | hyx⟩ := (mem_neighbors _ _ _).mp hy
  · exact (h.edgeScale x y hxy).2
  · exact (h.edgeScale y x hyx).1

end EarlyNormal

namespace ScaleTrigger

def path {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) :=
  ScaleWalks.shortestPath s.rows.active trigger.low trigger.high trigger.connected

theorem reaches {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) :
    p.A ^ p.J * s.width trigger.low ≤ s.width trigger.path.walk.finish := by
  rw [trigger.path.finish]
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right p.one_le_A (Nat.le_succ p.J))).trans
    trigger.steep.le

def vertices {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) : Fin p.J → Fin n :=
  trigger.path.walk.selected s.width p.A (s.width trigger.low) p.J p.one_le_A trigger.reaches

theorem vertices_bounds {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) :
    p.A ^ i.val * s.width trigger.low ≤ s.width (trigger.vertices i) ∧
      s.width (trigger.vertices i) ≤ p.width.L * (p.A ^ i.val * s.width trigger.low) := by
  refine ⟨trigger.path.walk.selected_lower _ _ _ _ _ _ i, ?_⟩
  apply trigger.path.walk.selected_upper s.width p.width.L p.A (s.width trigger.low) p.J
    (by have := p.width.two_le_L; omega) p.one_le_A
  · rw [trigger.path.start]
  · intro k
    exact closed_neighbor_width _ _ _ (by have := p.width.two_le_L; omega)
      normal.scaleBound _ _ (trigger.path.walk.step k)

theorem vertices_separated_lt {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) {i j : Fin p.J} (hij : i < j) :
    trigger.vertices j ∉ ball s.rows.active (trigger.vertices i) (2 * p.H) :=
  selected_separated trigger.path.walk s.width p.width.L p.A (s.width trigger.low) p.J (2 * p.H)
    (by have := p.width.two_le_L; omega) p.one_le_A (s.width_pos _)
    (by rw [trigger.path.start]) trigger.reaches normal.scaleBound p.gap hij

theorem vertices_separated {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) {i j : Fin p.J} (hij : i ≠ j) :
    trigger.vertices j ∉ ball s.rows.active (trigger.vertices i) (2 * p.H) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact trigger.vertices_separated_lt normal h
  · exact fun hball => trigger.vertices_separated_lt normal h (ball_symm _ hball)

theorem vertices_injective {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) : Function.Injective trigger.vertices := by
  intro i j heq
  by_contra hne
  have h := trigger.vertices_separated normal hne
  rw [heq] at h
  exact h (center_mem_ball _ _ _)

theorem vertices_incident {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) :
    (neighbors s.rows.active (trigger.vertices i)).Nonempty :=
  selected_nonisolated trigger.path.walk s.width p.width.L p.A (s.width trigger.low) p.J (2 * p.H)
    (by have := p.width.two_le_L; omega) p.one_le_A (s.width_pos _)
    (by have := p.group; omega) (by rw [trigger.path.start]) trigger.reaches normal.scaleBound p.gap i

theorem vertices_incomparable {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) {d : ℕ}
    (g : LocalOracle.SparseBounds s.rows p.H d) {i j : Fin p.J} (hij : i ≠ j) :
    s.numerical.system.edge (trigger.vertices i) (trigger.vertices j) = false ∧
      s.numerical.system.edge (trigger.vertices j) (trigger.vertices i) = false := by
  have h := incomparable_of_separated s.rows.active g.rank p.H g.strict g.height
    (trigger.vertices i) (trigger.vertices j) (trigger.vertices_separated normal hij)
  simpa only [State.numerical, closeSystem, SourcePartition.view, lookup_tableClosure] using h

def lower {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) (i : ℕ) : ℕ :=
  if hi : i < p.J then intervalLower s.numerical (trigger.vertices ⟨i, hi⟩) else 0

def upper {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) (i : ℕ) : ℕ :=
  if hi : i < p.J then intervalUpper s.numerical (trigger.vertices ⟨i, hi⟩) else 0

def widths {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) (i : ℕ) : ℕ :=
  if hi : i < p.J then s.width (trigger.vertices ⟨i, hi⟩) else 0

@[simp] theorem lower_fin {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) (i : Fin p.J) :
    trigger.lower i.val = intervalLower s.numerical (trigger.vertices i) := by simp [lower]

@[simp] theorem upper_fin {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) (i : Fin p.J) :
    trigger.upper i.val = intervalUpper s.numerical (trigger.vertices i) := by simp [upper]

def blocks {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) : List Block :=
  selectPaletteGroup s.order trigger.lower trigger.upper p.J

theorem blocks_length {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) : trigger.blocks.length = p.J := by
  apply selectPaletteGroup_length s.order trigger.widths trigger.lower trigger.upper
    p.A p.width.L (s.width trigger.low) p.J p.one_le_A p.veto_gap
  · intro i hi
    simpa only [widths, dif_pos hi] using trigger.vertices_bounds normal ⟨i, hi⟩
  · intro i hi
    simp only [upper, dif_pos hi]
    exact interval_upper_le s.numerical s.numerical_feasible _
  · intro i hi
    simp only [upper, lower, dif_pos hi]
    apply interval_large s.numerical s.numerical_feasible
    rw [s.numerical_width]
    exact p.width.large.trans (normal.wide _ (trigger.vertices_incident normal ⟨i, hi⟩))
  · intro i hi
    simp only [upper, lower, widths, dif_pos hi]
    simpa only [s.numerical_width] using (interval_length s.numerical s.numerical_feasible _).2
  · intro i hi
    simp only [upper, lower, widths, dif_pos hi]
    simpa only [s.numerical_width] using (interval_length s.numerical s.numerical_feasible _).1

theorem blocks_nodup {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) : trigger.blocks.Nodup :=
  selectPaletteGroup_nodup s.order trigger.lower trigger.upper p.J

def block {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) : Block :=
  trigger.blocks[i.val]'(by rw [trigger.blocks_length normal]; exact i.isLt)

theorem block_interior {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) :
    intervalLower s.numerical (trigger.vertices i) < chosenRank s.order (trigger.block normal i) ∧
      chosenRank s.order (trigger.block normal i) + 1 < intervalUpper s.numerical (trigger.vertices i) := by
  have h := selectPaletteGroup_get_interior s.order trigger.lower trigger.upper p.J i.val
    (by change i.val < trigger.blocks.length; rw [trigger.blocks_length normal]; exact i.isLt)
  simpa only [lower_fin, upper_fin, block, blocks, chosenRank] using h

def colour {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) : Fin (s.pool.palette + 1) :=
  ⟨chosenRank s.order (trigger.block normal i), by
    have h := (trigger.block_interior normal i).2
    have hK := interval_upper_le s.numerical s.numerical_feasible (trigger.vertices i)
    omega⟩

theorem colour_mem {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) :
    intervalLower s.numerical (trigger.vertices i) ≤ (trigger.colour normal i).val ∧
      (trigger.colour normal i).val < intervalUpper s.numerical (trigger.vertices i) := by
  have h := trigger.block_interior normal i
  change _ ≤ chosenRank _ _ ∧ chosenRank _ _ < _
  omega

theorem colour_interior {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) (i : Fin p.J) :
    s.pool.system.effectiveLower (trigger.vertices i) < trigger.colour normal i ∧
      trigger.colour normal i < s.pool.system.effectiveUpper (trigger.vertices i) := by
  have h := trigger.block_interior normal i
  have hw := interval_bounds s.numerical s.numerical_feasible (trigger.vertices i)
  have he := s.rows.view_windows s.pool.pin_bounds s.pool.invariant.feasible (trigger.vertices i)
  have hh : s.numerical.system.effectiveLower (trigger.vertices i) < trigger.colour normal i ∧
      trigger.colour normal i < s.numerical.system.effectiveUpper (trigger.vertices i) := by
    simp only [Fin.lt_def, colour]
    omega
  change (closeSystem s.rows.view).effectiveLower _ < _ ∧ _ < (closeSystem s.rows.view).effectiveUpper _ at hh
  rwa [he.1, he.2] at hh

theorem colour_multiplicity {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p) (c : ℕ) :
    (trigger.blocks.toFinset.filter (fun a => hubColour (paletteRank s.order)
      (paletteRank_injective s.order) a = c)).card ≤ 2 :=
  selectPaletteGroup_multiplicity s.order trigger.lower trigger.upper p.J c

end ScaleTrigger

end SortingAdversary.Optimal.WidthRepair
