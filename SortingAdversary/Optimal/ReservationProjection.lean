import SortingAdversary.Optimal.GroupReservations

/-!
# Reservation ledgers follow the actual incidence actions

Every real admission is also a reservation admission, and every real
promotion consumes its location in every reservation ledger. Physical
comparison records do not change either free set. This projection preserves
accepted execution, including a pending group of another promotion kind.
-/

namespace SortingAdversary.Optimal.ReservationProjection

open IncidenceLedger (Location)

variable {n : ℕ}

abbrev Book (n : ℕ) := GroupReservations.State (Location n)

structure Sync (book : Book n) (ledger : IncidenceLedger.State n) : Prop where
  entered : book.entered = ledger.entered
  free : book.free = ledger.free

def actions : IncidenceLedger.Action n → List (GroupReservations.Action (Location n))
  | .admit x => [.admit x]
  | .physical _ => []
  | .promote x _ => [.consume x]

def project (events : List (IncidenceLedger.Action n)) :
    List (GroupReservations.Action (Location n)) := events.flatMap actions

theorem run_append {α : Type*} [DecidableEq α] (s : GroupReservations.State α)
    (before after : List (GroupReservations.Action α)) :
    GroupReservations.run s (before ++ after) =
      (GroupReservations.run s before).bind (fun t => GroupReservations.run t after) := by
  induction before generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.cons_append, GroupReservations.run]
    cases h : GroupReservations.step s a with
    | none => rfl
    | some t => exact ih t

theorem step (threshold : ℕ) {ledger next : IncidenceLedger.State n}
    (a : IncidenceLedger.Action n) (h : IncidenceLedger.step threshold ledger a = some next)
    (book : Book n) (hs : Sync book ledger) :
    ∃ after : Book n,
      GroupReservations.run book (actions a) = some after ∧
      Sync after next ∧ after.pending ⊆ book.pending ∧ after.groups = book.groups := by
  cases a with
  | admit x =>
    simp only [IncidenceLedger.step] at h
    split at h
    next hx =>
      cases h
      refine ⟨{ book with entered := insert x book.entered, free := insert x book.free }, ?_,
        ⟨by simp [hs.entered], by simp [hs.free]⟩, Finset.Subset.refl _, rfl⟩
      simp [actions, GroupReservations.run, GroupReservations.step, hs.entered, hx]
    next => contradiction
  | physical row =>
    simp only [IncidenceLedger.step] at h
    split at h
    · cases h
      exact ⟨book, rfl, ⟨hs.entered, hs.free⟩, Finset.Subset.refl _, rfl⟩
    · contradiction
  | promote x kind =>
    simp only [IncidenceLedger.step] at h
    split at h
    next hx =>
      cases h
      refine ⟨{ book with free := book.free.erase x, pending := book.pending.erase x }, ?_,
        ⟨hs.entered, by simp [hs.free]⟩, Finset.erase_subset _ _, rfl⟩
      simp [actions, GroupReservations.run, GroupReservations.step, hs.free, hx.1]
    next => contradiction

theorem run (threshold : ℕ) (events : List (IncidenceLedger.Action n))
    {ledger next : IncidenceLedger.State n}
    (h : IncidenceLedger.run threshold ledger events = some next)
    (book : Book n) (hs : Sync book ledger) :
    ∃ after : Book n,
      GroupReservations.run book (project events) = some after ∧
      Sync after next ∧ after.pending ⊆ book.pending ∧ after.groups = book.groups := by
  induction events generalizing ledger book with
  | nil =>
    simp only [IncidenceLedger.run, Option.some.injEq] at h
    subst next
    exact ⟨book, rfl, hs, Finset.Subset.refl _, rfl⟩
  | cons a rest ih =>
    simp only [IncidenceLedger.run] at h
    cases he : IncidenceLedger.step threshold ledger a with
    | none => simp [he] at h
    | some mid =>
      simp only [he, Option.bind_some] at h
      obtain ⟨first, hf, hsf, hpf, hgf⟩ := step threshold a he book hs
      obtain ⟨last, hl, hsl, hpl, hgl⟩ := ih h first hsf
      refine ⟨last, ?_, hsl, hpl.trans hpf, hgl.trans hgf⟩
      change GroupReservations.run book (actions a ++ project rest) = some last
      rw [run_append, hf, Option.bind_some, hl]

theorem reserve (book : Book n) (members : Finset (Location n))
    (hempty : book.pending = ∅) (hne : members.Nonempty) (hfree : members ⊆ book.free) :
    GroupReservations.run book [.reserve members] =
      some { book with pending := members, groups := members :: book.groups } := by
  simp [GroupReservations.run, GroupReservations.step, hempty, hne, hfree]

theorem pending_empty {book : Book n} (hv : GroupReservations.Valid book)
    (members : Finset (Location n)) (hsub : book.pending ⊆ members)
    (hdone : ∀ x ∈ members, x ∉ book.free) : book.pending = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hdone x (hsub hx) (hv.pending_free hx)

end SortingAdversary.Optimal.ReservationProjection
