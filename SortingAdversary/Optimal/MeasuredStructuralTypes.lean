import SortingAdversary.Optimal.MeasuredPath
import SortingAdversary.Optimal.LongestPathWork
import SortingAdversary.Optimal.RepairSelectWork

/-! Assembly and erased correctness certificates for the measured outer repair loop. -/

namespace SortingAdversary.Optimal.MeasuredStructuralNormalize

open WidthRepair StructuralNormalize RepresentationWork LocalOracle PoolState
open SparseRepairGraph GraphBalls

set_option maxRecDepth 8192

variable {n : ℕ}

def degreeResult (s : State n) (p : Parameters) (width : WidthResult s p.scale)
    (ordinary : OrdinaryPromotion.Move width.final)
    (selected : degreeWitness width.final.rows.active width.final.pool.free p.D =
      some ordinary.update.vertex)
    (incident : (neighbors width.final.rows.active ordinary.update.vertex).Nonempty)
    (rest : StructuralNormalize.Result ordinary.update.next p) : StructuralNormalize.Result s p where
  final := rest.final
  trace := width.trace.append (.cons (.pin ordinary.update) rest.trace)
  events := .degree width.trace width.events ordinary selected rest.trace rest.events
  incident := width.trace.incidentFrom_append _ width.incident
    ⟨incident.mono (SparseRepairGraph.neighbors_mono _ _ width.trace.active_old _),
      rest.trace.incidentFrom_mono (width.trace.append (MeasuredPath.one ordinary)).active_old rest.incident⟩
  bound := rest.bound
  normal := rest.normal
  degree := rest.degree
  height := rest.height

def pathResult (s : State n) (p : Parameters) (width : WidthResult s p.scale)
    (selected : degreeWitness width.final.rows.active width.final.pool.free p.D = none)
    (reservation : Reservation width.final p.H)
    (group : PathResult p width.final width.final reservation reservation.labels)
    (rest : StructuralNormalize.Result group.final p) : StructuralNormalize.Result s p where
  final := rest.final
  trace := width.trace.append (group.trace.append rest.trace)
  events := .path width.trace width.events selected reservation group.trace group.events group.done rest.trace rest.events
  incident := width.trace.incidentFrom_append _ width.incident
    (group.trace.incidentFrom_append rest.trace
      (group.trace.incidentFrom_mono width.trace.active_old group.incident)
      (rest.trace.incidentFrom_mono (width.trace.append group.trace).active_old rest.incident))
  bound := rest.bound
  normal := rest.normal
  degree := rest.degree
  height := rest.height

def finishResult (s : State n) (p : Parameters)
    (g : SparseBounds s.rows p.scale.H p.d) (width : WidthResult s p.scale)
    (selected : degreeWitness width.final.rows.active width.final.pool.free p.D = none)
    (hlong : ¬ p.H ≤ (longestChain width.final.rows.active g.rank p.scale.H).length) :
    StructuralNormalize.Result s p where
  final := width.final
  trace := width.trace
  events := .finish width.trace width.events selected
  incident := width.incident
  bound := width.bound
  normal := width.normal
  degree := by
    intro v
    by_cases hi : (neighbors width.final.rows.active v).Nonempty
    · exact (degreeWitness_none _ _ _).mp selected v
        ((width.final.pool.free_iff v).mpr (width.final.nonisolated_free hi))
    · have he : neighbors width.final.rows.active v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
      rw [he, Finset.card_empty]
      exact p.degree_pos
  height := by
    intro path hpath
    exact (longestChain_maximal width.final.rows.active g.rank p.scale.H
      (width.trace.sparseBounds g).strict (fun v => g.height v) hpath).trans_lt (Nat.lt_of_not_ge hlong)

theorem degree_actual (s : State n) (p : Parameters)
    (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B)
    (width : WidthResult s p.scale) (hw : width = normalizeWidths s p.scale p.d g hB)
    (v : Fin n) (selected : degreeWitness width.final.rows.active width.final.pool.free p.D = some v)
    (incident : (neighbors width.final.rows.active v).Nonempty)
    (ordinary : OrdinaryPromotion.Move width.final)
    (ho : ordinary = OrdinaryPromotion.make width.final p.scale.H p.d (width.trace.sparseBounds g)
      p.scale.R (by positivity) v (width.normal.markCondition p.d (1 / 16) p.minimum v)
      ((width.final.pool.free_iff v).mp (degreeWitness_some _ _ _ selected).1)
      (width.final.nonisolated_mate incident))
    (vertex : ordinary.update.vertex = v)
    (rest : StructuralNormalize.Result ordinary.update.next p)
    (hr : rest = StructuralNormalize.normalize ordinary.update.next p
      ((MeasuredPath.one ordinary).sparseBounds (width.trace.sparseBounds g))
      (comparableBound_trace (MeasuredPath.one ordinary) width.bound)) :
    degreeResult s p width ordinary (by rw [vertex]; exact selected)
      (by rw [vertex]; exact incident) rest = StructuralNormalize.normalize s p g hB := by
  subst width
  subst ordinary
  subst rest
  conv_rhs => rw [StructuralNormalize.normalize]
  split
  · rename_i v' hsel
    have hv : v' = v := Option.some.inj (hsel.symm.trans selected)
    subst v'
    rfl
  · rename_i hsel
    simp only [hsel, reduceCtorEq] at selected

theorem path_actual (s : State n) (p : Parameters)
    (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B)
    (width : WidthResult s p.scale) (hw : width = normalizeWidths s p.scale p.d g hB)
    (selected : degreeWitness width.final.rows.active width.final.pool.free p.D = none)
    (hlong : p.H ≤ (longestChain width.final.rows.active g.rank p.scale.H).length)
    (reservation : Reservation width.final p.H)
    (hrsv : reservation = reservePath width.final p (width.trace.sparseBounds g) hlong)
    (group : PathResult p width.final width.final reservation reservation.labels)
    (hgroup : group = executePath width.final p reservation (width.trace.sparseBounds g) width.bound)
    (rest : StructuralNormalize.Result group.final p)
    (hr : rest = StructuralNormalize.normalize group.final p
      (group.trace.sparseBounds (width.trace.sparseBounds g)) group.bound) :
    pathResult s p width selected reservation group rest = StructuralNormalize.normalize s p g hB := by
  subst width
  subst reservation
  subst group
  subst rest
  conv_rhs => rw [StructuralNormalize.normalize]
  split
  · rename_i v hsel
    simp only [hsel, reduceCtorEq] at selected
  · split
    · rfl
    · contradiction

theorem finish_actual (s : State n) (p : Parameters)
    (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B)
    (width : WidthResult s p.scale) (hw : width = normalizeWidths s p.scale p.d g hB)
    (selected : degreeWitness width.final.rows.active width.final.pool.free p.D = none)
    (hlong : ¬ p.H ≤ (longestChain width.final.rows.active g.rank p.scale.H).length) :
    finishResult s p g width selected hlong = StructuralNormalize.normalize s p g hB := by
  subst width
  conv_rhs => rw [StructuralNormalize.normalize]
  split
  · rename_i v hsel
    simp only [hsel, reduceCtorEq] at selected
  · split
    · contradiction
    · rfl

theorem reservation_ext {s : State n} {H : ℕ} {a b : Reservation s H}
    (h : a.labels = b.labels) : a = b := by
  cases a
  cases b
  cases h
  rfl

def reservationFrom (s : State n) (p : Parameters) (g : SparseBounds s.rows p.scale.H p.d)
    (hlong : p.H ≤ (longestChain s.rows.active g.rank p.scale.H).length)
    (labels : List (Fin n)) (he : labels = reserve s.rows.active g.rank p.scale.H p.H) :
    Reservation s p.H :=
  let hs := reserve_spec s.rows.active g.rank p.scale.H p.H g.strict (fun v => g.height v) hlong
  ⟨labels, by rw [he]; exact hs.1, by rw [he]; exact hs.2.1, by rw [he]; exact hs.2.2⟩

theorem reservationFrom_actual (s : State n) (p : Parameters)
    (g : SparseBounds s.rows p.scale.H p.d)
    (hlong : p.H ≤ (longestChain s.rows.active g.rank p.scale.H).length)
    (labels : List (Fin n)) (he : labels = reserve s.rows.active g.rank p.scale.H p.H) :
    reservationFrom s p g hlong labels he = reservePath s p g hlong := reservation_ext he

structure Output (s : State n) (p : Parameters)
    (g : SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B) where
  result : StructuralNormalize.Result s p
  access : LocalAccess result.final
  actual : result = StructuralNormalize.normalize s p g hB
  cached : AccessBound access 2

end SortingAdversary.Optimal.MeasuredStructuralNormalize
