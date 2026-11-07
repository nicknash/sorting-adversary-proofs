import SortingAdversary.Optimal.StructuralNormalize
import SortingAdversary.Optimal.PrimitiveWork

/-!
# The actual repair loop's finite control schedule

The concrete executor already returns chronological event constructors.
Reading them gives the control schedule below: every priority scan, ordinary
or scale promotion, finite index-list creation, and trace concatenation is
accounted for. The list is ghost instrumentation; its own construction is
not recursively charged. Numerical kernel costs are supplied by the counted
implementations in the companion work modules.

This is a bound on the real event structure, not an independently supplied
iteration count. A completed path group must remove a formerly free label,
and a completed scale group contains its actual positive number of pins.
Those facts pay for every repeated outer invocation.
-/

namespace SortingAdversary.Optimal.RepairControlWork

open WidthRepair StructuralNormalize

variable {n : ℕ}

theorem trace_append_length {s t u : State n} (first : Trace s t) (second : Trace t u) :
    (first.append second).length = first.length + second.length := by
  induction first with
  | nil => simp [Trace.append, Trace.length]
  | cons head tail ih => simp only [Trace.append, Trace.length, ih]; omega

inductive Invocation where
  | earlyScan
  | scaleScan
  | degreeScan
  | longestPath
  | primitive
  | ordinary
  | scalePin
  | pathCheck
  | indices (length : ℕ)
  | copyTrace (length : ℕ)
  | control (operations : ℕ)
  deriving DecidableEq, Repr

def early {p : WidthParameters} {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p trace) : List Invocation :=
  match events with
  | .nil _ => [.earlyScan, .control 1]
  | .cons _ _ _ tail => [.earlyScan, .primitive, .control 6] ++ early tail

theorem early_length {p : WidthParameters} {s t : State n} {trace : Trace s t}
    (events : EarlyEvents p trace) : (early events).length = 3 * trace.length + 2 := by
  induction events with
  | nil => rfl
  | cons _ _ _ _ ih => simp only [early, List.length_append, List.length_cons,
      List.length_nil, Trace.length, ih]; omega

def scale {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n} {trace : Trace s t}
    {pending : List (Fin p.J)} (events : ScaleEvents start p trigger normal trace pending) :
    List Invocation :=
  match events with
  | .nil _ => [.control 1]
  | .cons _ _ _ _ _ _ _ _ tail => [.scalePin, .control 8] ++ scale tail

theorem scale_length {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n} {trace : Trace s t}
    {pending : List (Fin p.J)} (events : ScaleEvents start p trigger normal trace pending) :
    (scale events).length = 2 * trace.length + 1 ∧ trace.length = pending.length := by
  induction events with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ _ _ _ _ ih =>
    simp only [scale, List.length_append, List.length_cons, List.length_nil, Trace.length]
    omega

def widths {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (events : WidthEvents p trace) : List Invocation :=
  match events with
  | .early _ events => early events ++ [.scaleScan, .control 1]
  | .scale first firstEvents _ _ _ group groupEvents _ restEvents =>
      early firstEvents ++ [.scaleScan, .indices p.J, .control 2] ++ scale groupEvents ++
        widths restEvents ++ [.copyTrace group.length, .copyTrace first.length, .control 1]

theorem widths_length_le {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (events : WidthEvents p trace) : (widths events).length ≤ 11 * trace.length + 4 := by
  induction events with
  | early tr ev =>
    simp only [widths, List.length_append, early_length, List.length_cons, List.length_nil]
    omega
  | @scale s a b t first firstEvents trigger selected normal group groupEvents rest restEvents ih =>
    have hg := scale_length groupEvents
    have hJ := p.J_pos
    simp only [List.length_finRange] at hg
    simp only [widths, List.length_append, early_length, hg.1, List.length_cons,
      List.length_nil, trace_append_length]
    omega

def path {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : List Invocation :=
  match events with
  | .nil _ => [.control 1]
  | .skip _ _ before widthEvents _ _ tail =>
      widths widthEvents ++ [.pathCheck, .copyTrace before.length, .control 1] ++ path tail
  | .move _ _ before widthEvents _ _ _ tail =>
      widths widthEvents ++ [.pathCheck, .ordinary, .copyTrace before.length, .control 1] ++ path tail

theorem path_length_le {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) :
    (path events).length ≤ 11 * trace.length + 8 * pending.length + 1 := by
  induction events with
  | nil => simp [path, Trace.length]
  | skip _ _ before ev _ _ _ ih =>
    have hw := widths_length_le ev
    simp only [path, List.length_append, List.length_cons, List.length_nil, trace_append_length]
    omega
  | move _ _ before ev _ _ _ _ ih =>
    have hw := widths_length_le ev
    simp only [path, List.length_append, List.length_cons, List.length_nil, trace_append_length,
      Trace.length]
    omega

def structural {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) : List Invocation :=
  match events with
  | .finish _ widthEvents _ => widths widthEvents ++ [.degreeScan, .longestPath, .control 1]
  | .degree before widthEvents _ _ _ tail =>
      widths widthEvents ++ [.degreeScan, .ordinary, .control 1] ++ structural tail ++
        [.copyTrace before.length]
  | .path before widthEvents _ _ group groupEvents _ _ tail =>
      widths widthEvents ++ [.degreeScan, .longestPath, .longestPath, .indices p.H, .control 1] ++
        path groupEvents ++ structural tail ++ [.copyTrace group.length, .copyTrace before.length]

private theorem trace_length_pos_of_lost {s t : State n} (trace : Trace s t) (v : Fin n)
    (hs : v ∈ s.pool.free) (ht : v ∉ t.pool.free) : 0 < trace.length := by
  cases trace with
  | nil => exact False.elim (ht hs)
  | cons => simp [Trace.length]

theorem structural_length_le {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    (structural events).length ≤ (8 * n + 24) * trace.length + 7 := by
  induction events with
  | finish before ev _ =>
    have hw := widths_length_le ev
    have hm : 11 * before.length ≤ (8 * n + 24) * before.length :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [structural, List.length_append, List.length_cons, List.length_nil]
    omega
  | @degree s a t before ev ordinary selected rest tail ih =>
    have hw := widths_length_le ev
    have hm : 11 * before.length ≤ (8 * n + 24) * before.length :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [structural, List.length_append, List.length_cons, List.length_nil,
      trace_append_length, Trace.length, Nat.mul_add]
    omega
  | @path s a b t before ev degree reservation group groupEvents completed rest tail ih =>
    have hw := widths_length_le ev
    have hp := path_length_le groupEvents
    have hH : p.H ≤ n := by
      rw [← reservation.length]
      simpa only [Fintype.card_fin] using reservation.nodup.length_le_card
    have hnonempty : reservation.labels ≠ [] := by
      intro hz
      have hlen := reservation.length
      rw [hz] at hlen
      have htwo := p.path_two
      simp only [List.length_nil] at hlen
      omega
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil reservation.labels hnonempty
    have hg := trace_length_pos_of_lost group v (reservation.free p.path_two hv) (completed v hv)
    rw [reservation.length] at hp
    have hm : 11 * before.length ≤ (8 * n + 24) * before.length :=
      Nat.mul_le_mul_right _ (by omega)
    have hpaid : 11 * group.length + 8 * p.H + 12 ≤ (8 * n + 24) * group.length := by
      have ht : 8 * n + 13 ≤ (8 * n + 13) * group.length := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (8 * n + 13) hg
      have he : (8 * n + 24) * group.length = 11 * group.length + (8 * n + 13) * group.length := by
        rw [← Nat.add_mul]
        congr 1
        omega
      rw [he]
      omega
    simp only [structural, List.length_append, List.length_cons, List.length_nil,
      trace_append_length, Nat.mul_add]
    omega

/-- An actual result of the concrete normalizer supplies every control
bound without a separate execution or iteration assumption. -/
theorem normalize_control_bound (s : State n) (p : Parameters)
    (g : LocalOracle.SparseBounds s.rows p.scale.H p.d) (hB : ComparableBound s p.scale.width.B) :
    (structural (normalize s p g hB).events).length ≤ (8 * n + 24) * (n + n * n) + 7 := by
  have h := structural_length_le (normalize s p g hB).events
  have ht := (normalize s p g hB).steps_le_quadratic
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ ht) _)

def work (charge : Invocation → ℕ) (schedule : List Invocation) : ℕ :=
  (schedule.map charge).sum

theorem work_le (charge : Invocation → ℕ) (schedule : List Invocation) (bound : ℕ)
    (h : ∀ call ∈ schedule, charge call ≤ bound) : work charge schedule ≤ schedule.length * bound := by
  induction schedule with
  | nil => simp [work]
  | cons call rest ih =>
    have hh := h call (List.mem_cons_self ..)
    have ht := ih (fun next hn => h next (List.mem_cons_of_mem call hn))
    simp only [work, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    change work charge rest ≤ _ at ht
    change charge call + work charge rest ≤ _
    omega

theorem structural_work_le {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) (charge : Invocation → ℕ) (bound : ℕ)
    (h : ∀ call ∈ structural events, charge call ≤ bound) :
    work charge (structural events) ≤ ((8 * n + 24) * trace.length + 7) * bound :=
  (work_le charge _ bound h).trans (Nat.mul_le_mul_right _ (structural_length_le events))

end SortingAdversary.Optimal.RepairControlWork

