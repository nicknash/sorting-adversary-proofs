import SortingAdversary.Optimal.MeasuredWidthTypes
import SortingAdversary.Optimal.MeasuredOrdinaryTypes
import SortingAdversary.Optimal.StructuralNormalize

/-!
# Uniform envelopes for composing measured repair executors

Every repair step removes at least one unit of the finite repair measure
and creates at most one colour. Their sum therefore bounds every palette
encountered by the actual recursive execution. The executor bounds in this
module are intermediate composition interfaces; the final program supplies
the concrete measured routines and discharges them.
-/

namespace SortingAdversary.Optimal.MeasuredRepairBounds

open WidthRepair RepresentationWork LocalOracle StructuralNormalize

variable {n : ℕ}

def size (s : State n) : ℕ := s.pool.palette + s.measure

theorem trace_size_le {s t : State n} (trace : Trace s t) : size t ≤ size s := by
  have hp := RepresentationWork.trace_palette_le trace
  have hm := trace.length_add_measure_le
  unfold size
  omega

theorem pin_size_le {s : State n} (update : PinUpdate s) : size update.next ≤ size s :=
  trace_size_le (.cons (.pin update) (.nil _))

theorem measure_le (s : State n) : s.measure ≤ n + n * n := by
  have hf : s.pool.free.card ≤ n := by simpa using Finset.card_le_univ s.pool.free
  have hr := SparseRepairGraph.rawRows_card_le s.rows.active
  unfold State.measure
  omega

theorem trace_length_le {s t : State n} (trace : Trace s t) : trace.length ≤ n + n * n := by
  have hm := trace.length_add_measure_le
  have hs := measure_le s
  omega

def WidthBound (executor : MeasuredWidthNormalize.Executor n) (p : ScaleParameters)
    (d cap work : ℕ) : Prop :=
  ∀ {s : State n} (a : LocalAccess s) (ha : AccessBound a 2)
    (g : SparseBounds s.rows p.H d) (hB : ComparableBound s p.width.B),
    size s ≤ cap → (executor a ha p d g hB).work ≤ work

def OrdinaryBound (p : Parameters)
    (executor : MeasuredOrdinaryPromotion.Executor n p.scale.H p.d p.scale.R)
    (cap work : ℕ) : Prop :=
  ∀ {s : State n} (a : LocalAccess s) (ha : AccessBound a 2)
    (g : SparseBounds s.rows p.scale.H p.d) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view p.scale.H p.d p.scale.R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : SeparatedPins.HasMate s.pool v),
    size s ≤ cap →
      (executor a ha g (by positivity) v hmark hv hm).work ≤ work

end SortingAdversary.Optimal.MeasuredRepairBounds
