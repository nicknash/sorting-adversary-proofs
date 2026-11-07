import SortingAdversary.Optimal.LedgerStructuralReplay
import SortingAdversary.Optimal.ReservationProjection

/-!
# Reservation boundaries extracted from the concrete normalizer

The annotations below retain the exact primitive trace and its actual pin
classifications. A reserved path may contain scale reservations. Reservations
of the same kind cannot nest. Every group starts with free members and its
recorded body ends with all of those members no longer free.
-/

namespace SortingAdversary.Optimal.ReservationAnnotations

open WidthRepair LedgerReplayLabels LedgerStructuralReplay

variable {n : ℕ}

inductive Program (H J : ℕ) : Bool → Bool → {s t : State n} → Trace s t → Type
  | nil (pathBusy scaleBusy : Bool) (s : State n) :
      Program H J pathBusy scaleBusy (.nil s)
  | cons {pathBusy scaleBusy : Bool} {s a t : State n}
      (step : Step s a) (label : StepLabel step) (tail : Trace a t)
      (rest : Program H J pathBusy scaleBusy tail) :
      Program H J pathBusy scaleBusy (.cons step tail)
  | append {pathBusy scaleBusy : Bool} {s a t : State n}
      (first : Trace s a) (second : Trace a t)
      (before : Program H J pathBusy scaleBusy first)
      (after : Program H J pathBusy scaleBusy second) :
      Program H J pathBusy scaleBusy (first.append second)
  | path {scaleBusy : Bool} {s t : State n} (trace : Trace s t)
      (members : Finset (Fin n)) (nonempty : members.Nonempty)
      (card : members.card = H) (free : members ⊆ s.pool.free)
      (completed : ∀ v ∈ members, v ∉ t.pool.free)
      (body : Program H J true scaleBusy trace) :
      Program H J false scaleBusy trace
  | scale {pathBusy : Bool} {s t : State n} (trace : Trace s t)
      (members : Finset (Fin n)) (nonempty : members.Nonempty)
      (card : members.card = J) (free : members ⊆ s.pool.free)
      (completed : ∀ v ∈ members, v ∉ t.pool.free)
      (body : Program H J pathBusy true trace) :
      Program H J pathBusy false trace

def Program.labels {H J : ℕ} {pb sb : Bool} {s t : State n}
    {trace : Trace s t} (program : Program H J pb sb trace) : Labels trace :=
  match program with
  | .nil .. => PUnit.unit
  | .cons _ label _ rest => (label, rest.labels)
  | .append first second before after => Labels.append first second before.labels after.labels
  | .path _ _ _ _ _ _ body => body.labels
  | .scale _ _ _ _ _ _ body => body.labels

def plain (H J : ℕ) (pathBusy scaleBusy : Bool) : {s t : State n} →
    (trace : Trace s t) → Labels trace → Program H J pathBusy scaleBusy trace
  | _, _, .nil s, _ => .nil pathBusy scaleBusy s
  | _, _, .cons step tail, labels =>
      .cons step labels.1 tail (plain H J pathBusy scaleBusy tail labels.2)

@[simp] theorem plain_labels (H J : ℕ) (pb sb : Bool) {s t : State n}
    (trace : Trace s t) (labels : Labels trace) : (plain H J pb sb trace labels).labels = labels := by
  induction trace with
  | nil => cases labels; rfl
  | cons step tail ih => exact Prod.ext rfl (ih labels.2)

def Program.pathGroups {H J : ℕ} {pb sb : Bool} {s t : State n}
    {trace : Trace s t} (program : Program H J pb sb trace) : List (Finset (Fin n)) :=
  match program with
  | .nil .. => []
  | .cons _ _ _ rest => rest.pathGroups
  | .append _ _ before after => before.pathGroups ++ after.pathGroups
  | .path _ members _ _ _ _ body => members :: body.pathGroups
  | .scale _ _ _ _ _ _ body => body.pathGroups

def Program.scaleGroups {H J : ℕ} {pb sb : Bool} {s t : State n}
    {trace : Trace s t} (program : Program H J pb sb trace) : List (Finset (Fin n)) :=
  match program with
  | .nil .. => []
  | .cons _ _ _ rest => rest.scaleGroups
  | .append _ _ before after => before.scaleGroups ++ after.scaleGroups
  | .path _ _ _ _ _ _ body => body.scaleGroups
  | .scale _ members _ _ _ _ body => members :: body.scaleGroups

theorem Program.pathGroups_card {H J : ℕ} {pb sb : Bool} {s t : State n}
    {trace : Trace s t} (program : Program H J pb sb trace) :
    ∀ members ∈ program.pathGroups, members.card = H := by
  induction program with
  | nil => simp [Program.pathGroups]
  | cons _ _ _ _ ih => exact ih
  | append _ _ _ _ ih₁ ih₂ =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ih₁ g hg
      · exact ih₂ g hg
  | path _ members _ card _ _ _ ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact card
      · exact ih g hg
  | scale _ _ _ _ _ _ _ ih => exact ih

theorem Program.scaleGroups_card {H J : ℕ} {pb sb : Bool} {s t : State n}
    {trace : Trace s t} (program : Program H J pb sb trace) :
    ∀ members ∈ program.scaleGroups, members.card = J := by
  induction program with
  | nil => simp [Program.scaleGroups]
  | cons _ _ _ _ ih => exact ih
  | append _ _ _ _ ih₁ ih₂ =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ih₁ g hg
      · exact ih₂ g hg
  | path _ _ _ _ _ _ _ ih => exact ih
  | scale _ members _ card _ _ _ ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact card
      · exact ih g hg

theorem scale_completed {start : State n} {p : ScaleParameters} {trigger : ScaleTrigger start p}
    {normal : EarlyNormal start p.width.W₀ p.width.L} {s t : State n}
    {trace : Trace s t} {indices : List (Fin p.J)}
    (events : ScaleEvents start p trigger normal trace indices) :
    ∀ i ∈ indices, trigger.vertices i ∉ t.pool.free := by
  induction events with
  | nil => simp
  | @cons s t i update vertex _ _ _ _ rest indices events ih =>
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · intro hfree
        have h := rest.free_subset hfree
        rw [← vertex] at h
        change update.vertex ∈ (s.pool.installPromotion update.vertex update.free
          update.colour update.result).free at h
        rw [PoolState.Pool.installPromotion_free] at h
        exact (Finset.mem_erase.mp h).1 rfl
      · exact ih j hj

theorem scale_free {s : State n} {p : ScaleParameters} (trigger : ScaleTrigger s p)
    (normal : EarlyNormal s p.width.W₀ p.width.L) :
    Finset.univ.image trigger.vertices ⊆ s.pool.free := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact (s.pool.free_iff _).mpr (s.nonisolated_free (trigger.vertices_incident normal i))

def width {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (H : ℕ) (pathBusy : Bool) (events : WidthEvents p trace) :
    Program H p.J pathBusy false trace :=
  match events with
  | .early trace events => plain H p.J pathBusy false trace (earlyLabels events)
  | .scale early earlyEvents trigger _ normal group groupEvents rest restEvents =>
      .append early (group.append rest)
        (plain H p.J pathBusy false early (earlyLabels earlyEvents))
        (.append group rest
          (.scale group (Finset.univ.image trigger.vertices)
            (by
              obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp p.J_pos
              exact ⟨trigger.vertices i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
            (by rw [Finset.card_image_of_injective _ (trigger.vertices_injective normal)]; simp)
            (scale_free trigger normal)
            (by
              intro v hv
              obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
              exact scale_completed groupEvents i (List.mem_finRange _))
            (plain H p.J pathBusy true group (scaleLabels groupEvents)))
          (width H pathBusy restEvents))

def path {p : StructuralNormalize.Parameters} {start : State n}
    {reservation : StructuralNormalize.Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : StructuralNormalize.PathEvents p start reservation trace pending) :
    Program p.H p.scale.J true false trace :=
  match events with
  | .nil s => .nil true false s
  | .skip _ _ widths widthEvents _ rest events =>
      .append widths rest (width p.H true widthEvents) (path events)
  | .move _ _ widths widthEvents ordinary _ rest events =>
      .append widths (.cons (.pin ordinary.update) rest) (width p.H true widthEvents)
        (.cons (.pin ordinary.update) .path rest (path events))

def structural {p : StructuralNormalize.Parameters} {s t : State n} {trace : Trace s t}
    (events : StructuralNormalize.Events p trace) :
    Program p.H p.scale.J false false trace :=
  match events with
  | .finish _ widthEvents _ => width p.H false widthEvents
  | .degree widths widthEvents ordinary _ rest events =>
      .append widths (.cons (.pin ordinary.update) rest) (width p.H false widthEvents)
        (.cons (.pin ordinary.update) .degree rest (structural events))
  | .path widths widthEvents _ reservation group groupEvents completed rest events =>
      .append widths (group.append rest) (width p.H false widthEvents)
        (.append group rest
          (.path group reservation.labels.toFinset
            (by
              apply Finset.card_pos.mp
              rw [List.toFinset_card_of_nodup reservation.nodup, reservation.length]
              exact lt_of_lt_of_le (by decide : 0 < 2) p.path_two)
            (by rw [List.toFinset_card_of_nodup reservation.nodup, reservation.length])
            (by
              intro v hv
              exact reservation.free p.path_two (List.mem_toFinset.mp hv))
            (by simpa only [List.mem_toFinset] using completed)
            (path groupEvents))
          (structural events))

@[simp] theorem width_labels {p : ScaleParameters} {s t : State n} {trace : Trace s t}
    (H : ℕ) (pb : Bool) (events : WidthEvents p trace) :
    (width H pb events).labels = widthLabels events := by
  induction events with
  | early => simp only [width, plain_labels, widthLabels]
  | scale early earlyEvents trigger selected normal group groupEvents rest restEvents ih =>
      simp only [width, Program.labels, plain_labels, widthLabels, ih]

@[simp] theorem path_labels {p : StructuralNormalize.Parameters} {start : State n}
    {reservation : StructuralNormalize.Reservation start p.H}
    {s t : State n} {trace : Trace s t} {pending : List (Fin n)}
    (events : StructuralNormalize.PathEvents p start reservation trace pending) :
    (path events).labels = pathLabels events := by
  induction events with
  | nil => rfl
  | skip _ _ widths widthEvents _ rest events ih =>
      simp only [path, Program.labels, width_labels, pathLabels, ih]
  | move _ _ widths widthEvents ordinary _ rest events ih =>
      simp only [path, Program.labels, width_labels, pathLabels, ih]

@[simp] theorem structural_labels {p : StructuralNormalize.Parameters} {s t : State n}
    {trace : Trace s t} (events : StructuralNormalize.Events p trace) :
    (structural events).labels = structuralLabels events := by
  induction events with
  | finish => simp only [structural, width_labels, structuralLabels]
  | degree widths widthEvents ordinary selected rest events ih =>
      simp only [structural, Program.labels, width_labels, structuralLabels, ih]
  | path widths widthEvents degree reservation group groupEvents completed rest events ih =>
      simp only [structural, Program.labels, width_labels, path_labels, structuralLabels, ih]

end SortingAdversary.Optimal.ReservationAnnotations
