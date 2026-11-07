import SortingAdversary.Optimal.ReservationFits
import SortingAdversary.Optimal.RepairGroupHubs

/-!
# Actual normalizer groups have final destination multiplicity one or two

Path members retain their original comparison-chain exclusion even when
width cleanup moves them. Scale members use the actual selected hub blocks.
The proofs below follow the emitted normalizer events and their final pins.
-/

namespace SortingAdversary.Optimal.ReservationFits

open WidthRepair PoolState StructuralNormalize RepairPricing StoredEvolution
open ReservationAnnotations LedgerReplayLabels

variable {n : ℕ}

theorem trace_evolution {s t : State n} (trace : Trace s t) : LocalEvolution s t := by
  induction trace with
  | nil s => exact .refl s
  | cons head tail ih => exact (LocalEvolution.step head).trans ih

theorem Local.advance {s t : State n} {members : Finset (Fin n)} {cap : ℕ}
    (h : Local s members cap) (trace : Trace s t) : Local t members cap :=
  h.evolution (trace_evolution trace)

theorem scale_pins {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n}
    {trace : Trace s t} {indices : List (Fin p.J)}
    (events : ScaleEvents start p trigger normal trace indices) (view : ScaleView start s) :
    ∀ i ∈ indices, (scaleEvent trigger normal i).Fits t := by
  induction events with
  | nil => simp
  | cons i update vertex colour interior palette charge rest events ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact (scaleEvent_fits trigger normal view j update vertex colour interior).advance rest
    · exact ih (view.advance update interior palette) j hj

theorem scale_local {s t : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) {trace : Trace s t}
    (events : ScaleEvents s p trigger normal trace (List.finRange p.J)) :
    Local t (Finset.univ.image trigger.vertices) 2 := by
  have hp (i : Fin p.J) : (scaleEvent trigger normal i).Fits t :=
    scale_pins events (ScaleView.refl s) i (List.mem_finRange i)
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    have hi := hp i
    obtain ⟨c, hc, _⟩ := hi.pinned
    change t.pool.pins (trigger.vertices i) = some c at hc
    exact Finset.mem_filter.mpr ⟨hi.member, by simp [hc]⟩
  · intro identity
    have he : (Finset.univ.image trigger.vertices).filter (fun v => destination t v = some identity) =
        (Finset.univ.filter (fun i : Fin p.J => (scaleEvent trigger normal i).identity = identity)).image
          trigger.vertices := by
      ext v
      constructor
      · intro hv
        obtain ⟨hv, hd⟩ := Finset.mem_filter.mp hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        exact immutablePin_unique (hp i).pinned (destination_iff.mp hd)
      · intro hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [← (Finset.mem_filter.mp hi).2]
        exact destination_iff.mpr (hp i).pinned
    rw [he]
    exact Finset.card_image_le.trans (scale_destination_multiplicity trigger normal identity)

theorem path_local {s t : State n} {H : ℕ} (reservation : Reservation s H) (hH : 2 ≤ H)
    (trace : Trace s t) (completed : ∀ v ∈ reservation.labels, v ∉ t.pool.free) :
    Local t reservation.labels.toFinset 1 := by
  apply of_completed _ 1
  · intro v hv
    rw [trace.members]
    exact (Finset.mem_filter.mp (reservation.free hH (List.mem_toFinset.mp hv))).1
  · simpa only [List.mem_toFinset] using completed
  · exact reservation_destination_multiplicity reservation hH trace

@[simp] theorem plain_paths (H J : ℕ) (pb sb : Bool) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) :
    (plain H J pb sb trace labels).pathGroups = [] := by
  induction trace with
  | nil => rfl
  | cons head tail ih => exact ih labels.2

@[simp] theorem plain_scales (H J : ℕ) (pb sb : Bool) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) :
    (plain H J pb sb trace labels).scaleGroups = [] := by
  induction trace with
  | nil => rfl
  | cons head tail ih => exact ih labels.2

@[simp] theorem width_paths {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (H : ℕ) (pb : Bool) (events : WidthEvents p trace) :
    (width H pb events).pathGroups = [] := by
  induction events with
  | early => simp only [width, plain_paths]
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    simp only [width, Program.pathGroups, plain_paths, ih, List.nil_append]

@[simp] theorem path_paths {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) : (path events).pathGroups = [] := by
  induction events with
  | nil => rfl
  | skip _ _ width widthEvents _ rest events ih =>
      simp only [path, Program.pathGroups, width_paths, ih, List.nil_append]
  | move _ _ width widthEvents ordinary _ rest events ih =>
      simp only [path, Program.pathGroups, width_paths, ih, List.nil_append]

theorem width_scales {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (H : ℕ) (pb : Bool) (events : WidthEvents p trace) :
    ∀ members ∈ (width H pb events).scaleGroups, Local t members 2 := by
  induction events with
  | early => simp only [width, plain_scales, List.not_mem_nil, false_implies, implies_true]
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
    intro members hm
    simp only [width, Program.scaleGroups, plain_scales, List.nil_append,
      List.cons_append, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact (scale_local trigger normal groupEvents).advance rest
    · exact ih members hm

theorem path_scales {p : Parameters} {start : State n} {reservation : Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : PathEvents p start reservation trace pending) :
    ∀ members ∈ (path events).scaleGroups, Local t members 2 := by
  induction events with
  | nil => simp [path, Program.scaleGroups]
  | skip _ _ widths widthEvents _ rest events ih =>
    intro members hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (width_scales p.H true widthEvents members hm).advance rest
    · exact ih members hm
  | move _ _ widths widthEvents ordinary _ rest events ih =>
    intro members hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (width_scales p.H true widthEvents members hm).advance (.cons (.pin ordinary.update) rest)
    · exact ih members hm

theorem structural_paths {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    ∀ members ∈ (structural events).pathGroups, Local t members 1 := by
  induction events with
  | finish => simp only [structural, width_paths, List.not_mem_nil, false_implies, implies_true]
  | degree widths widthEvents ordinary selected rest events ih =>
    simpa only [structural, Program.pathGroups, width_paths, List.nil_append] using ih
  | path widths widthEvents degree reservation group groupEvents completed rest events ih =>
    intro members hm
    simp only [structural, Program.pathGroups, width_paths, path_paths,
      List.nil_append, List.cons_append, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact path_local reservation p.path_two (group.append rest)
        (fun v hv hf => completed v hv (rest.free_subset hf))
    · exact ih members hm

theorem structural_scales {p : Parameters} {s t : State n} {trace : Trace s t}
    (events : Events p trace) :
    ∀ members ∈ (structural events).scaleGroups, Local t members 2 := by
  induction events with
  | finish widths widthEvents _ => exact width_scales p.H false widthEvents
  | degree widths widthEvents ordinary selected rest events ih =>
    intro members hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (width_scales p.H false widthEvents members hm).advance (.cons (.pin ordinary.update) rest)
    · exact ih members hm
  | path widths widthEvents degree reservation group groupEvents completed rest events ih =>
    intro members hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (width_scales p.H false widthEvents members hm).advance (group.append rest)
    · rcases List.mem_append.mp hm with hm | hm
      · exact (path_scales groupEvents members hm).advance rest
      · exact ih members hm

end SortingAdversary.Optimal.ReservationFits
