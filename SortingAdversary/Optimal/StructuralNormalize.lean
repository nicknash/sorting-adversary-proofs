import SortingAdversary.Optimal.WidthScale
import SortingAdversary.Optimal.OrdinaryPromotion

/-!
# Concrete degree and reserved-path normalization

The executable controller completely repairs widths before each ordinary
promotion. It takes a current high-degree label first, otherwise a fixed
prefix of an actual longest directed path. A reserved label is still moved
when its last numerical incident row has disappeared; its original public
comparison mate and endpoint incidence survive as proof certificates.
-/

namespace SortingAdversary.Optimal.StructuralNormalize

set_option maxRecDepth 8192

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState LocalOracle
open GraphBalls SparseRepairGraph SeparatedPins

variable {n : ℕ}

/-- Maintenance bounds are distinct from the tighter ordinary stopping caps.
All numerical local-oracle premises are supplied by the completed width loop. -/
structure Parameters where
  scale : ScaleParameters
  d : ℕ
  D : ℕ
  H : ℕ
  degree_pos : 0 < D
  path_two : 2 ≤ H
  minimum : LocalParameters.minimumWidth scale.H (LocalAccuracy.influenceSize scale.H d)
    scale.R (1 / 16) ≤ scale.width.W₀

/-- Every label of a nontrivial actual path has a proper incident row. -/
theorem chain_incident (E : Fin n → Fin n → Bool) {path : List (Fin n)}
    (hchain : path.IsChain (fun x y => Arc E y x)) (hlength : 2 ≤ path.length)
    {v : Fin n} (hv : v ∈ path) : (neighbors E v).Nonempty := by
  induction path with
  | nil => simp at hv
  | cons a tail ih =>
    cases tail with
    | nil => simp at hlength
    | cons b rest =>
      have hh := List.isChain_cons_cons.mp hchain
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨b, (mem_neighbors _ _ _).mpr ⟨hh.1.1, Or.inr hh.1.2⟩⟩
      · cases rest with
        | nil =>
          have hb : v = b := by simpa only [List.mem_singleton] using hv
          subst v
          exact ⟨a, (mem_neighbors _ _ _).mpr ⟨hh.1.1.symm, Or.inl hh.1.2⟩⟩
        | cons c rest => exact ih hh.2 (by simp) hv

/-- A fixed original path reservation, retaining its actual raw-edge and
public-order witnesses after later width cleanups remove numerical rows. -/
structure Reservation (s : State n) (H : ℕ) where
  labels : List (Fin n)
  length : labels.length = H
  nodup : labels.Nodup
  chain : labels.IsChain (fun x y => Arc s.rows.active y x)

namespace Reservation

variable {s : State n} {H : ℕ}

theorem incident (r : Reservation s H) (hH : 2 ≤ H) {v : Fin n} (hv : v ∈ r.labels) :
    (neighbors s.rows.active v).Nonempty :=
  chain_incident s.rows.active r.chain (by rw [r.length]; exact hH) hv

theorem free (r : Reservation s H) (hH : 2 ≤ H) {v : Fin n} (hv : v ∈ r.labels) :
    v ∈ s.pool.free := (s.pool.free_iff v).mpr (s.nonisolated_free (r.incident hH hv))

theorem mate (r : Reservation s H) (hH : 2 ≤ H) {v : Fin n} (hv : v ∈ r.labels) :
    HasMate s.pool v := s.nonisolated_mate (r.incident hH hv)

theorem public_order (r : Reservation s H) :
    r.labels.Pairwise (fun x y => s.pool.system.edge y x = true) :=
  chain_public_pairwise s.rows.active s.pool.system.edge
    s.pool.invariant.closed.trans (fun _ _ h => s.rows.active_public h) r.chain

end Reservation

/-- Reserve the actual materialized longest-path table's first `H` labels. -/
def reservePath (s : State n) (p : Parameters) (g : SparseBounds s.rows p.scale.H p.d)
    (hlong : p.H ≤ (longestChain s.rows.active g.rank p.scale.H).length) : Reservation s p.H :=
  let hs := reserve_spec s.rows.active g.rank p.scale.H p.H g.strict
    (fun v => g.height v) hlong
  ⟨reserve s.rows.active g.rank p.scale.H p.H, hs.1, hs.2.1, hs.2.2⟩

/-- Repair stages preserve the public pool while only removing active rows. -/
structure Context (start current : State n) : Prop where
  members : current.pool.members = start.pool.members
  edges : current.pool.system.edge = start.pool.system.edge
  active : ∀ x y, current.rows.active x y = true → start.rows.active x y = true

namespace Context

variable {s t u : State n}

theorem refl (s : State n) : Context s s := ⟨rfl, rfl, fun _ _ h => h⟩

theorem advance (h : Context s t) (trace : Trace t u) : Context s u :=
  ⟨trace.members.trans h.members, trace.public_edges.trans h.edges,
    fun x y hxy => h.active x y (trace.active_old x y hxy)⟩

theorem mate (h : Context s t) {v : Fin n} (hv : HasMate s.pool v) : HasMate t.pool v :=
  hasMate_of_same_public h.members h.edges hv

end Context

end SortingAdversary.Optimal.StructuralNormalize

namespace SortingAdversary.Optimal.WidthRepair

open PoolState

variable {n : ℕ}

theorem Step.free_subset {s t : State n} (step : Step s t) : t.pool.free ⊆ s.pool.free := by
  cases step with
  | pin update =>
    change (s.pool.installPromotion update.vertex update.free update.colour update.result).free ⊆ _
    rw [Pool.installPromotion_free]
    exact Finset.erase_subset _ _
  | lowerCut => exact Finset.Subset.refl _
  | upperCut => exact Finset.Subset.refl _

theorem Trace.free_subset {s t : State n} (trace : Trace s t) : t.pool.free ⊆ s.pool.free := by
  induction trace with
  | nil => exact Finset.Subset.refl _
  | cons head tail ih => exact ih.trans head.free_subset

theorem Trace.measure_lt_of_lost {s t : State n} (trace : Trace s t) {v : Fin n}
    (hold : v ∈ s.pool.free) (hnew : v ∉ t.pool.free) : t.measure < s.measure := by
  cases trace with
  | nil => exact False.elim (hnew hold)
  | cons head tail =>
    have htail := tail.length_add_measure_le
    exact (by omega : t.measure ≤ _).trans_lt head.measure_lt

end SortingAdversary.Optimal.WidthRepair

namespace SortingAdversary.Optimal.StructuralNormalize

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState LocalOracle
open GraphBalls SparseRepairGraph SeparatedPins

variable {n : ℕ}

/-- Exact chronological annotations for a reserved group. Every iteration
first executes the full width loop, then either observes an already moved
label or performs an ordinary promotion with its actual priced hub record. -/
inductive PathEvents (p : Parameters) (start : State n) (reservation : Reservation start p.H) :
    {s t : State n} → Trace s t → List (Fin n) → Type
  | nil (s : State n) : PathEvents p start reservation (.nil s) []
  | skip {s a t : State n} (v : Fin n) (reserved : v ∈ reservation.labels)
      (width : Trace s a) (widthEvents : WidthEvents p.scale width)
      (moved : v ∉ a.pool.free) (rest : Trace a t) {pending : List (Fin n)}
      (events : PathEvents p start reservation rest pending) :
      PathEvents p start reservation (width.append rest) (v :: pending)
  | move {s a t : State n} (v : Fin n) (reserved : v ∈ reservation.labels)
      (width : Trace s a) (widthEvents : WidthEvents p.scale width)
      (ordinary : OrdinaryPromotion.Move a) (vertex : ordinary.update.vertex = v)
      (rest : Trace ordinary.update.next t) {pending : List (Fin n)}
      (events : PathEvents p start reservation rest pending) :
      PathEvents p start reservation (width.append (.cons (.pin ordinary.update) rest)) (v :: pending)

structure PathResult (p : Parameters) (start current : State n)
    (reservation : Reservation start p.H) (pending : List (Fin n)) where
  final : State n
  trace : Trace current final
  events : PathEvents p start reservation trace pending
  incident : trace.IncidentFrom start.rows.active
  bound : ComparableBound final p.scale.width.B
  done : ∀ v ∈ pending, v ∉ final.pool.free

/-- Even an isolated final reserved label is promoted: the oracle has its
exact isolated-coordinate branch, while the original path supplies its mate. -/
def runPath (p : Parameters) (start current : State n) (reservation : Reservation start p.H)
    (pending : List (Fin n)) (subset : ∀ v ∈ pending, v ∈ reservation.labels)
    (context : Context start current)
    (g : SparseBounds current.rows p.scale.H p.d) (hB : ComparableBound current p.scale.width.B) :
    PathResult p start current reservation pending :=
  match pending with
  | [] => ⟨current, .nil current, .nil current, trivial, hB, by simp⟩
  | v :: pending =>
    let width := normalizeWidths current p.scale p.d g hB
    let nextContext := context.advance width.trace
    if hfree : width.final.pool.pins v = none then
      let ordinary := OrdinaryPromotion.make width.final p.scale.H p.d (width.trace.sparseBounds g)
        p.scale.R (by positivity) v (width.normal.markCondition p.d (1 / 16) p.minimum v) hfree
        (nextContext.mate (reservation.mate p.path_two (subset v (List.mem_cons_self ..))))
      let one : Trace width.final ordinary.update.next := .cons (.pin ordinary.update) (.nil _)
      let rest := runPath p start ordinary.update.next reservation pending
        (fun x hx => subset x (List.mem_cons_of_mem v hx)) (nextContext.advance one)
        (one.sparseBounds (width.trace.sparseBounds g))
        (comparableBound_trace one width.bound)
      ⟨rest.final, width.trace.append (.cons (.pin ordinary.update) rest.trace),
        .move v (subset v (List.mem_cons_self ..)) width.trace width.events ordinary rfl rest.trace rest.events,
        width.trace.incidentFrom_append _
          (width.trace.incidentFrom_mono context.active width.incident)
          ⟨reservation.incident p.path_two (subset v (List.mem_cons_self ..)), rest.incident⟩,
        rest.bound, by
          intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · intro hf
            have hh := rest.trace.free_subset hf
            rw [heq] at hh
            change v ∈ (width.final.pool.installPromotion ordinary.update.vertex ordinary.update.free
              ordinary.update.colour ordinary.update.result).free at hh
            rw [Pool.installPromotion_free] at hh
            exact (Finset.mem_erase.mp hh).1 rfl
          · exact rest.done x hx⟩
    else
      let rest := runPath p start width.final reservation pending
        (fun x hx => subset x (List.mem_cons_of_mem v hx)) nextContext
        (width.trace.sparseBounds g) width.bound
      let hmoved : v ∉ width.final.pool.free := fun h => hfree ((width.final.pool.free_iff v).mp h)
      ⟨rest.final, width.trace.append rest.trace,
        .skip v (subset v (List.mem_cons_self ..)) width.trace width.events hmoved rest.trace rest.events,
        width.trace.incidentFrom_append rest.trace
          (width.trace.incidentFrom_mono context.active width.incident) rest.incident,
        rest.bound, by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact fun hf => hmoved (rest.trace.free_subset hf)
          · exact rest.done x hx⟩

def executePath (s : State n) (p : Parameters) (reservation : Reservation s p.H)
    (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B) :
    PathResult p s s reservation reservation.labels :=
  runPath p s s reservation reservation.labels (fun _ h => h) (Context.refl s) g hB

theorem executePath_measure_lt (s : State n) (p : Parameters) (reservation : Reservation s p.H)
    (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B) :
    (executePath s p reservation g hB).final.measure < s.measure := by
  have hnonempty : reservation.labels ≠ [] := by
    intro hz
    have h := reservation.length
    rw [hz] at h
    have := p.path_two
    simp only [List.length_nil] at h
    omega
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil reservation.labels hnonempty
  exact (executePath s p reservation g hB).trace.measure_lt_of_lost
    (reservation.free p.path_two hv) ((executePath s p reservation g hB).done v hv)

end SortingAdversary.Optimal.StructuralNormalize

namespace SortingAdversary.Optimal.StructuralNormalize

open WeakMaps WeakMaps.WeakSystem WidthRepair PoolState LocalOracle
open GraphBalls SparseRepairGraph SeparatedPins

variable {n : ℕ}

/-- A complete execution records the priority test and each actual ordinary
hub. Path reservations retain all their intervening width operations. -/
inductive Events (p : Parameters) : {s t : State n} → Trace s t → Type
  | finish {s t : State n} (width : Trace s t) (widthEvents : WidthEvents p.scale width)
      (degree : degreeWitness t.rows.active t.pool.free p.D = none) : Events p width
  | degree {s a t : State n} (width : Trace s a) (widthEvents : WidthEvents p.scale width)
      (ordinary : OrdinaryPromotion.Move a)
      (selected : degreeWitness a.rows.active a.pool.free p.D = some ordinary.update.vertex)
      (rest : Trace ordinary.update.next t) (events : Events p rest) :
      Events p (width.append (.cons (.pin ordinary.update) rest))
  | path {s a b t : State n} (width : Trace s a) (widthEvents : WidthEvents p.scale width)
      (degree : degreeWitness a.rows.active a.pool.free p.D = none)
      (reservation : Reservation a p.H)
      (group : Trace a b) (groupEvents : PathEvents p a reservation group reservation.labels)
      (completed : ∀ v ∈ reservation.labels, v ∉ b.pool.free)
      (rest : Trace b t) (events : Events p rest) :
      Events p (width.append (group.append rest))

structure Result (s : State n) (p : Parameters) where
  final : State n
  trace : Trace s final
  events : Events p trace
  incident : trace.IncidentFrom s.rows.active
  bound : ComparableBound final p.scale.width.B
  normal : WidthNormal final p.scale
  degree : ∀ v, (neighbors final.rows.active v).card < p.D
  height : ∀ path : List (Fin n), path.IsChain (fun x y => Arc final.rows.active y x) → path.length < p.H

/-- The complete deterministic ordinary loop, with the real width executor
at every priority boundary and no unresolved oracle or repair callback. -/
def normalize (s : State n) (p : Parameters) (g : SparseBounds s.rows p.scale.H p.d)
    (hB : ComparableBound s p.scale.width.B) : Result s p :=
  let width := normalizeWidths s p.scale p.d g hB
  let graph := width.trace.sparseBounds g
  match selected : degreeWitness width.final.rows.active width.final.pool.free p.D with
  | some v =>
    let hs := degreeWitness_some width.final.rows.active width.final.pool.free p.D selected
    let incident : (neighbors width.final.rows.active v).Nonempty :=
      Finset.card_pos.mp (p.degree_pos.trans_le hs.2)
    let ordinary := OrdinaryPromotion.make width.final p.scale.H p.d graph p.scale.R (by positivity)
      v (width.normal.markCondition p.d (1 / 16) p.minimum v) ((width.final.pool.free_iff v).mp hs.1)
      (width.final.nonisolated_mate incident)
    let one : Trace width.final ordinary.update.next := .cons (.pin ordinary.update) (.nil _)
    let rest := normalize ordinary.update.next p (one.sparseBounds graph)
      (comparableBound_trace one width.bound)
    ⟨rest.final, width.trace.append (.cons (.pin ordinary.update) rest.trace),
      .degree width.trace width.events ordinary selected rest.trace rest.events,
      width.trace.incidentFrom_append _ width.incident
        ⟨incident.mono (SparseRepairGraph.neighbors_mono _ _ width.trace.active_old v),
          rest.trace.incidentFrom_mono (width.trace.append one).active_old rest.incident⟩,
      rest.bound, rest.normal, rest.degree, rest.height⟩
  | none =>
    if hlong : p.H ≤ (longestChain width.final.rows.active graph.rank p.scale.H).length then
      let reservation := reservePath width.final p graph hlong
      let group := executePath width.final p reservation graph width.bound
      let rest := normalize group.final p (group.trace.sparseBounds graph) group.bound
      ⟨rest.final, width.trace.append (group.trace.append rest.trace),
        .path width.trace width.events selected reservation group.trace group.events group.done rest.trace rest.events,
        width.trace.incidentFrom_append _ width.incident
          (group.trace.incidentFrom_append rest.trace
            (group.trace.incidentFrom_mono width.trace.active_old group.incident)
            (rest.trace.incidentFrom_mono (width.trace.append group.trace).active_old rest.incident)),
        rest.bound, rest.normal, rest.degree, rest.height⟩
    else
      ⟨width.final, width.trace, .finish width.trace width.events selected, width.incident,
        width.bound, width.normal,
        by
          intro v
          by_cases hi : (neighbors width.final.rows.active v).Nonempty
          · exact (degreeWitness_none _ _ _).mp selected v
              ((width.final.pool.free_iff v).mpr (width.final.nonisolated_free hi))
          · have he : neighbors width.final.rows.active v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
            rw [he, Finset.card_empty]
            exact p.degree_pos,
        by
          intro path hpath
          exact (longestChain_maximal width.final.rows.active graph.rank p.scale.H graph.strict
            (fun v => graph.height v) hpath).trans_lt (Nat.lt_of_not_ge hlong)⟩
termination_by s.measure
decreasing_by
  all_goals
    have hwidth := width.trace.length_add_measure_le
  · exact ordinary.update.measure_lt.trans_le (by omega)
  · exact (executePath_measure_lt width.final p reservation graph width.bound).trans_le (by omega)

namespace Result

variable {s : State n} {p : Parameters}

/-- Compress the actual final longest-path table to the new target bounds.
The returned rank is executable and uses the original label carrier. -/
def sparseBounds (r : Result s p) (g : SparseBounds s.rows p.scale.H p.d) :
    SparseBounds r.final.rows p.H (p.D - 1) where
  rank := heightRank r.final.rows.active g.rank p.scale.H
  strict x y h := heightRank_strict r.final.rows.active g.rank p.scale.H
    (r.trace.sparseBounds g).strict (fun v => g.height v) h
  height v := by
    have h := heightRank_bound r.final.rows.active g.rank p.scale.H
      (r.trace.sparseBounds g).strict (fun w => g.height w) v
    have hl := r.height _ (longestChain_chain r.final.rows.active g.rank p.scale.H
      (r.trace.sparseBounds g).strict (fun w => g.height w))
    exact h.trans hl.le
  degree v := Nat.le_sub_one_of_lt (r.degree v)

theorem steps_le (r : Result s p) : r.trace.length ≤ s.measure := by
  have h := r.trace.length_add_measure_le
  omega

theorem steps_le_quadratic (r : Result s p) : r.trace.length ≤ n + n * n := by
  have hf : s.pool.free.card ≤ n := by simpa using Finset.card_le_univ s.pool.free
  exact r.steps_le.trans (Nat.add_le_add hf (SparseRepairGraph.rawRows_card_le _))

end Result

end SortingAdversary.Optimal.StructuralNormalize
