import SortingAdversary.Optimal.IncidenceLedger
import SortingAdversary.Optimal.GroupEntropy
import SortingAdversary.Optimal.HubSelector
import Mathlib.Data.List.Pairwise

/-!
# Disjoint chronological reservations and their actual entropy arrays

A reservation starts only after the preceding reservation of its type has
been consumed. Its members must be currently free. Admissions never return
an already entered label. The resulting disjointness is proved from these
executable checks, including when a reserved member is consumed by another
promotion type.

The second part constructs conditional-entropy arrays by counting actual
events, rather than accepting an array with unspecified row or column sums.
-/

namespace SortingAdversary.Optimal.GroupReservations

open scoped BigOperators

section Chronology

variable {α : Type*} [DecidableEq α]

structure State (α : Type*) where
  entered : Finset α
  free : Finset α
  pending : Finset α
  groups : List (Finset α)

def initial (free : Finset α) : State α := ⟨free, free, ∅, []⟩

structure Valid (s : State α) : Prop where
  free_entered : s.free ⊆ s.entered
  pending_free : s.pending ⊆ s.free
  group_entered : ∀ g ∈ s.groups, g ⊆ s.entered
  overlap_pending : ∀ g ∈ s.groups, ∀ x ∈ g, x ∈ s.free → x ∈ s.pending
  disjoint : s.groups.Pairwise Disjoint

omit [DecidableEq α] in
theorem initial_valid (free : Finset α) : Valid (initial free) := by
  constructor <;> simp [initial]

inductive Action (α : Type*) where
  | admit (label : α)
  | reserve (members : Finset α)
  | consume (label : α)

def step (s : State α) : Action α → Option (State α)
  | .admit x =>
    if x ∉ s.entered then some { s with entered := insert x s.entered, free := insert x s.free }
    else none
  | .reserve g =>
    if s.pending = ∅ ∧ g.Nonempty ∧ g ⊆ s.free then
      some { s with pending := g, groups := g :: s.groups }
    else none
  | .consume x =>
    if x ∈ s.free then some { s with free := s.free.erase x, pending := s.pending.erase x }
    else none

theorem step_valid {s t : State α} (hs : Valid s) (a : Action α) (ht : step s a = some t) :
    Valid t := by
  cases a with
  | admit x =>
    simp only [step] at ht
    split at ht
    next hx =>
      cases ht
      constructor
      · exact Finset.insert_subset_insert _ hs.free_entered
      · exact hs.pending_free.trans (Finset.subset_insert _ _)
      · intro g hg
        exact (hs.group_entered g hg).trans (Finset.subset_insert _ _)
      · intro g hg y hy hyfree
        rcases Finset.mem_insert.mp hyfree with heq | hold
        · exact False.elim (hx (heq ▸ hs.group_entered g hg hy))
        · exact hs.overlap_pending g hg y hy hold
      · exact hs.disjoint
    next => contradiction
  | reserve g =>
    simp only [step] at ht
    split at ht
    next h =>
      obtain ⟨hempty, _hne, hfree⟩ := h
      cases ht
      constructor
      · exact hs.free_entered
      · exact hfree
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hfree.trans hs.free_entered
        · exact hs.group_entered k hk
      · intro k hk x hx hxfree
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hx
        · have h := hs.overlap_pending k hk x hx hxfree
          simp [hempty] at h
      · apply List.pairwise_cons.mpr
        refine ⟨?_, hs.disjoint⟩
        intro k hk
        apply Finset.disjoint_left.mpr
        intro x hx hxk
        have h := hs.overlap_pending k hk x hxk (hfree hx)
        simp [hempty] at h
    next => contradiction
  | consume x =>
    simp only [step] at ht
    split at ht
    · cases ht
      constructor
      · exact (Finset.erase_subset _ _).trans hs.free_entered
      · intro y hy
        obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
        exact Finset.mem_erase.mpr ⟨hne, hs.pending_free hy⟩
      · exact hs.group_entered
      · intro g hg y hy hyfree
        obtain ⟨hne, hyfree⟩ := Finset.mem_erase.mp hyfree
        exact Finset.mem_erase.mpr ⟨hne, hs.overlap_pending g hg y hy hyfree⟩
      · exact hs.disjoint
    · contradiction

def run (s : State α) : List (Action α) → Option (State α)
  | [] => some s
  | a :: rest => (step s a).bind (fun t => run t rest)

theorem run_valid (actions : List (Action α)) {s t : State α}
    (hs : Valid s) (ht : run s actions = some t) : Valid t := by
  induction actions generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at ht
    exact ht ▸ hs
  | cons a rest ih =>
    simp only [run] at ht
    cases hstep : step s a with
    | none => simp [hstep] at ht
    | some u =>
      simp only [hstep, Option.bind_some] at ht
      exact ih (step_valid hs a hstep) ht

def consumed (s : State α) : Finset α := s.entered \ s.free

theorem completed_group_subset {s : State α} (hs : Valid s) (hcomplete : s.pending = ∅)
    (g : Finset α) (hg : g ∈ s.groups) : g ⊆ consumed s := by
  intro x hx
  apply Finset.mem_sdiff.mpr
  refine ⟨hs.group_entered g hg hx, ?_⟩
  intro hfree
  have h := hs.overlap_pending g hg x hx hfree
  simp [hcomplete] at h

omit [DecidableEq α] in
theorem indexed_groups_disjoint {s : State α} (hs : Valid s) :
    Pairwise (fun i j : Fin s.groups.length => Disjoint (s.groups.get i) (s.groups.get j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hs.disjoint.rel_get_of_lt hlt
  · exact (hs.disjoint.rel_get_of_lt hgt).symm

/-- Disjointness and actual consumption of each recorded group are derived
from the checked chronology, with no restriction on which type consumed a
reserved member. Instantiate this ledger separately for path and scale
reservations at each immutable node. -/
theorem accepted_reservations (free : Finset α) (actions : List (Action α)) (s : State α)
    (hrun : run (initial free) actions = some s) (hcomplete : s.pending = ∅) :
    Pairwise (fun i j : Fin s.groups.length => Disjoint (s.groups.get i) (s.groups.get j)) ∧
      ∀ i : Fin s.groups.length, s.groups.get i ⊆ consumed s := by
  have hs := run_valid actions (initial_valid free) hrun
  exact ⟨indexed_groups_disjoint hs, fun i =>
    completed_group_subset hs hcomplete _ (List.get_mem _ _)⟩

end Chronology

section EventArrays

variable {Event Group Child : Type*}
variable [Fintype Event] [Fintype Group] [Fintype Child]
variable [DecidableEq Event] [DecidableEq Group] [DecidableEq Child]

/-- Every cell is the exact number of actual events with this pair of group
and destination identities. -/
def cell (group : Event → Group) (destination : Event → Child) (g : Group) (c : Child) : ℝ :=
  (((Finset.univ.filter (fun e => group e = g)).filter
    (fun e => destination e = c)).card : ℝ)

def groupEvents (group : Event → Group) (g : Group) : Finset Event :=
  Finset.univ.filter (fun e => group e = g)

def destinationEvents (destination : Event → Child) (c : Child) : Finset Event :=
  Finset.univ.filter (fun e => destination e = c)

omit [Fintype Group] [Fintype Child] [DecidableEq Event] in
theorem cell_nonneg (group : Event → Group) (destination : Event → Child) (g : Group) (c : Child) :
    0 ≤ cell group destination g c := Nat.cast_nonneg _

omit [Fintype Group] [DecidableEq Event] in
theorem cell_groupSize (group : Event → Group) (destination : Event → Child) (g : Group) :
    GroupEntropy.groupSize (cell group destination) g = ((groupEvents group g).card : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := groupEvents group g)
    (t := Finset.univ) (f := destination) (fun _ _ => Finset.mem_univ _)
  unfold GroupEntropy.groupSize cell groupEvents
  exact_mod_cast h.symm

omit [Fintype Child] [DecidableEq Event] in
theorem cell_childSize (group : Event → Group) (destination : Event → Child) (c : Child) :
    GroupEntropy.childSize (cell group destination) c = ((destinationEvents destination c).card : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := destinationEvents destination c)
    (t := Finset.univ) (f := group) (fun _ _ => Finset.mem_univ _)
  unfold GroupEntropy.childSize cell
  simp only [Finset.filter_filter]
  simp only [destinationEvents, Finset.filter_filter, and_comm] at h
  exact_mod_cast h.symm

omit [DecidableEq Event] in
theorem cell_totalSize (group : Event → Group) (destination : Event → Child) :
    GroupEntropy.totalSize (cell group destination) = (Fintype.card Event : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
    (t := Finset.univ) (f := group) (fun _ _ => Finset.mem_univ _)
  unfold GroupEntropy.totalSize
  simp only [cell_groupSize]
  exact_mod_cast h.symm

noncomputable def destinationEntropy (destination : Event → Child) (reservoir : ℝ) : ℝ :=
  ∑ c, ((destinationEvents destination c).card : ℝ) *
    Real.log (reservoir / ((destinationEvents destination c).card : ℝ))

omit [DecidableEq Event] in
theorem cell_childEntropy (group : Event → Group) (destination : Event → Child) :
    GroupEntropy.childEntropy (cell group destination) =
      destinationEntropy destination (Fintype.card Event) := by
  simp [GroupEntropy.childEntropy, destinationEntropy, cell_childSize, cell_totalSize]

omit [DecidableEq Event] in
/-- Enlarging the reservoir from the actual promotion count to all admitted
labels can only increase the destination entropy budget. -/
theorem destinationEntropy_mono (destination : Event → Child) (reservoir : ℝ)
    (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    destinationEntropy destination (Fintype.card Event) ≤ destinationEntropy destination reservoir := by
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : (destinationEvents destination c).card = 0
  · simp [hc]
  have hkc : (0 : ℝ) < (destinationEvents destination c).card := by
    exact_mod_cast Nat.pos_of_ne_zero hc
  have hp : (0 : ℝ) < Fintype.card Event :=
    hkc.trans_le (by exact_mod_cast Finset.card_le_univ (destinationEvents destination c))
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (div_pos hp hkc) (div_le_div_of_nonneg_right hreservoir hkc.le)) hkc.le

omit [DecidableEq Event] in
/-- The group budget is now a theorem about counts of actual events. Row
sizes and per-destination multiplicities are elementary finite-set claims;
all column totals and the conditional-entropy comparison are derived. -/
theorem selected_event_budget (group : Event → Group) (destination : Event → Child)
    (selected : Finset Group) (h r : ℕ) (hr : 0 < r)
    (hsize : ∀ g ∈ selected, (groupEvents group g).card = h)
    (hcap : ∀ g ∈ selected, ∀ c, ((groupEvents group g).filter
      (fun e => destination e = c)).card ≤ r)
    (reservoir : ℝ) (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    ((selected.card : ℝ) * h) * Real.log ((h : ℝ) / r) ≤ destinationEntropy destination reservoir := by
  have hbudget := GroupEntropy.selected_group_budget (cell group destination)
    (cell_nonneg group destination) selected h r (by exact_mod_cast hr)
    (fun g hg => by rw [cell_groupSize, hsize g hg])
    (fun g hg c => by
      have h := hcap g hg c
      dsimp only [groupEvents] at h
      dsimp only [cell]
      exact_mod_cast h)
  rw [cell_childEntropy] at hbudget
  exact hbudget.trans (destinationEntropy_mono destination reservoir hreservoir)

end EventArrays

section DisjointGroups

variable {Event Child : Type*} [Fintype Event] [Fintype Child]
variable [DecidableEq Event] [DecidableEq Child] {G : ℕ}

def membershipIndices (groups : Fin G → Finset Event) (e : Event) : Finset (Fin G) :=
  Finset.univ.filter (fun g => e ∈ groups g)

/-- The finite lookup assigns every unreserved event to the extra `none`
row. Hence the conditional-entropy array includes all actual promotions. -/
def groupOf (groups : Fin G → Finset Event) (e : Event) : Option (Fin G) :=
  if h : (membershipIndices groups e).Nonempty then
    some ((membershipIndices groups e).min' h)
  else none

omit [Fintype Event] in
theorem groupOf_mem (groups : Fin G → Finset Event) (e : Event) (g : Fin G)
    (h : groupOf groups e = some g) : e ∈ groups g := by
  unfold groupOf at h
  split at h
  next hn =>
    have hm := Finset.min'_mem (membershipIndices groups e) hn
    have heq := Option.some.inj h
    rw [heq] at hm
    exact (Finset.mem_filter.mp hm).2
  next => contradiction

omit [Fintype Event] in
theorem groupOf_eq_some_iff (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) (e : Event) (g : Fin G) :
    groupOf groups e = some g ↔ e ∈ groups g := by
  refine ⟨groupOf_mem groups e g, ?_⟩
  intro he
  have hn : (membershipIndices groups e).Nonempty := ⟨g, by simp [membershipIndices, he]⟩
  have hm := Finset.min'_mem (membershipIndices groups e) hn
  have hmem := (Finset.mem_filter.mp hm).2
  have heq : (membershipIndices groups e).min' hn = g := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint hne) hmem he
  simp [groupOf, hn, heq]

theorem groupEvents_groupOf (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) (g : Fin G) :
    groupEvents (groupOf groups) (some g) = groups g := by
  ext e
  simp [groupEvents, groupOf_eq_some_iff groups hdisjoint]

def reservedEvents (groups : Fin G → Finset Event) : Finset Event := Finset.univ.biUnion groups

omit [Fintype Event] in
theorem reservedEvents_card (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) (h : ℕ)
    (hsize : ∀ g, (groups g).card = h) : (reservedEvents groups).card = G * h := by
  unfold reservedEvents
  rw [Finset.card_biUnion (fun i _ j _ hij => hdisjoint hij)]
  simp [hsize]

/-- The destination counts, leftover row, selected rows, and number of
reserved events are all computed from the actual disjoint finite groups. -/
theorem disjoint_group_budget (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (destination : Event → Child) (h r : ℕ) (hr : 0 < r)
    (hsize : ∀ g, (groups g).card = h)
    (hcap : ∀ g c, ((groups g).filter (fun e => destination e = c)).card ≤ r)
    (reservoir : ℝ) (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    ((reservedEvents groups).card : ℝ) * Real.log ((h : ℝ) / r) ≤
      destinationEntropy destination reservoir := by
  let selected : Finset (Option (Fin G)) := Finset.univ.image some
  have hcard : selected.card = G := by
    dsimp only [selected]
    rw [Finset.card_image_of_injective _ (Option.some_injective _)]
    simp
  have hbudget := selected_event_budget (groupOf groups) destination selected h r hr
    (fun g hg => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      rw [groupEvents_groupOf groups hdisjoint]
      exact hsize i)
    (fun g hg c => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      rw [groupEvents_groupOf groups hdisjoint]
      exact hcap i c)
    reservoir hreservoir
  rw [hcard] at hbudget
  simpa [reservedEvents_card groups hdisjoint h hsize, Nat.cast_mul] using hbudget

theorem disjoint_group_count_le (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (destination : Event → Child) (h r : ℕ) (hr : 0 < r) (hseparated : r < h)
    (hsize : ∀ g, (groups g).card = h)
    (hcap : ∀ g c, ((groups g).filter (fun e => destination e = c)).card ≤ r)
    (reservoir : ℝ) (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    ((reservedEvents groups).card : ℝ) ≤
      destinationEntropy destination reservoir / Real.log ((h : ℝ) / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hh' : (r : ℝ) < h := by exact_mod_cast hseparated
  apply (le_div_iff₀ (Real.log_pos ((one_lt_div hr').mpr hh'))).mpr
  exact disjoint_group_budget groups hdisjoint destination h r hr hsize hcap reservoir hreservoir

omit [Fintype Event] [Fintype Child] [DecidableEq Event] in
theorem injective_destination_cap (group : Finset Event) (destination : Event → Child)
    (hinjective : Set.InjOn destination group) (c : Child) :
    (group.filter (fun e => destination e = c)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hyc⟩ := Finset.mem_filter.mp hy
  exact hinjective hx hy (hxc.trans hyc.symm)

/-- Distinct destinations on each reserved path supply the path entropy
budget for the actual event population, including events outside paths. -/
theorem path_group_count_le (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (destination : Event → Child) (H : ℕ) (hH : 1 < H)
    (hsize : ∀ g, (groups g).card = H)
    (hinjective : ∀ g, Set.InjOn destination (groups g))
    (reservoir : ℝ) (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    ((reservedEvents groups).card : ℝ) ≤ destinationEntropy destination reservoir / Real.log H := by
  simpa using disjoint_group_count_le groups hdisjoint destination H 1 (by omega) hH hsize
    (fun g c => injective_destination_cap _ destination (hinjective g) c) reservoir hreservoir

end DisjointGroups

section ActualHubs

variable {Event : Type*} [DecidableEq Event]

omit [DecidableEq Event] in
/-- The two-per-destination scale cap is inherited from actual valid block
records and the singleton/nonsingleton veto. No multiplicity bound is assumed.
-/
theorem hub_destination_cap {K births : ℕ} (group : Finset Event)
    (destination : Event → Fin K) (record : Event → HubSelector.Block)
    (rank : ℕ → ℕ) (hinj : Function.Injective rank)
    (hvalid : ∀ e ∈ group, record e ∈ HubSelector.allBlocks births)
    (hrecord : Set.InjOn record group)
    (hdestination : ∀ e ∈ group, (destination e).val = HubSelector.hubColour rank hinj (record e))
    (c : Fin K) : (group.filter (fun e => destination e = c)).card ≤ 2 := by
  let selected := group.image record
  have hcap := HubSelector.selected_colour_multiplicity_le_two rank hinj selected
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact hvalid e he) c.val
  apply le_trans _ hcap
  apply Finset.card_le_card_of_injOn record
  · intro e he
    obtain ⟨he, hec⟩ := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    rw [← hdestination e he, hec]
  · intro e he e' he' heq
    exact hrecord (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he').1 heq

theorem scale_group_count_le [Fintype Event] {G K : ℕ}
    (groups : Fin G → Finset Event)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (destination : Event → Fin K) (J : ℕ) (hJ : 2 < J)
    (hsize : ∀ g, (groups g).card = J)
    (births : Fin G → ℕ) (record : Event → HubSelector.Block)
    (rank : Fin G → ℕ → ℕ) (hinj : ∀ g, Function.Injective (rank g))
    (hvalid : ∀ g e, e ∈ groups g → record e ∈ HubSelector.allBlocks (births g))
    (hrecord : ∀ g, Set.InjOn record (groups g))
    (hdestination : ∀ g e, e ∈ groups g →
      (destination e).val = HubSelector.hubColour (rank g) (hinj g) (record e))
    (reservoir : ℝ) (hreservoir : (Fintype.card Event : ℝ) ≤ reservoir) :
    ((reservedEvents groups).card : ℝ) ≤
      destinationEntropy destination reservoir / Real.log ((J : ℝ) / 2) := by
  exact disjoint_group_count_le groups hdisjoint destination J 2 (by omega) hJ hsize
    (fun g c => hub_destination_cap (groups g) destination record (rank g) (hinj g)
      (hvalid g) (hrecord g) (hdestination g) c) reservoir hreservoir

end ActualHubs

section CompletedChronology

variable {α : Type*} [DecidableEq α]

def subtypeGroup (pool members : Finset α) : Finset ↥pool :=
  Finset.univ.filter (fun x => x.val ∈ members)

theorem subtypeGroup_card (pool members : Finset α) (hsubset : members ⊆ pool) :
    (subtypeGroup pool members).card = members.card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    exact ⟨⟨x, hsubset hx⟩, by simp [subtypeGroup, hx], rfl⟩

theorem subtypeGroup_disjoint (pool a b : Finset α) (h : Disjoint a b) :
    Disjoint (subtypeGroup pool a) (subtypeGroup pool b) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

/-- The actual events in a completed reservation ledger are precisely labels
already consumed. The carrier omits every label which remains free. -/
def completedGroups (s : State α) (i : Fin s.groups.length) : Finset ↥(consumed s) :=
  subtypeGroup (consumed s) (s.groups.get i)

theorem completedGroups_disjoint {s : State α} (hs : Valid s) :
    Pairwise (fun i j => Disjoint (completedGroups s i) (completedGroups s j)) := by
  intro i j hij
  exact subtypeGroup_disjoint _ _ _ (indexed_groups_disjoint hs hij)

theorem completedGroups_card {s : State α} (hs : Valid s) (hcomplete : s.pending = ∅)
    (i : Fin s.groups.length) : (completedGroups s i).card = (s.groups.get i).card :=
  subtypeGroup_card _ _ (completed_group_subset hs hcomplete _ (List.get_mem _ _))

theorem consumed_card_le_entered (s : State α) : (consumed s).card ≤ s.entered.card :=
  Finset.card_le_card Finset.sdiff_subset

/-- The end-to-end path budget starts from an accepted chronological ledger.
Its only path-specific inputs are the selected path length and distinct final
destinations of its members. The entropy reservoir is the actual number of
labels ever admitted to this node. -/
theorem accepted_path_budget {Child : Type*} [Fintype Child] [DecidableEq Child]
    (free : Finset α) (actions : List (Action α)) (s : State α)
    (hrun : run (initial free) actions = some s) (hcomplete : s.pending = ∅)
    (destination : ↥(consumed s) → Child) (H : ℕ) (hH : 1 < H)
    (hsize : ∀ i : Fin s.groups.length, (s.groups.get i).card = H)
    (hinjective : ∀ i, Set.InjOn destination (completedGroups s i)) :
    ((reservedEvents (completedGroups s)).card : ℝ) ≤
      destinationEntropy destination s.entered.card / Real.log H := by
  have hs := run_valid actions (initial_valid free) hrun
  apply path_group_count_le (completedGroups s) (completedGroups_disjoint hs) destination H hH
    (fun i => (completedGroups_card hs hcomplete i).trans (hsize i)) hinjective
  exact_mod_cast (by simpa using consumed_card_le_entered s)

/-- The corresponding chronological scale budget obtains the destination
cap from actual dyadic records and the two-kind hub theorem. -/
theorem accepted_scale_budget {K : ℕ}
    (free : Finset α) (actions : List (Action α)) (s : State α)
    (hrun : run (initial free) actions = some s) (hcomplete : s.pending = ∅)
    (destination : ↥(consumed s) → Fin K) (J : ℕ) (hJ : 2 < J)
    (hsize : ∀ i : Fin s.groups.length, (s.groups.get i).card = J)
    (births : Fin s.groups.length → ℕ) (record : ↥(consumed s) → HubSelector.Block)
    (rank : Fin s.groups.length → ℕ → ℕ) (hinj : ∀ g, Function.Injective (rank g))
    (hvalid : ∀ g e, e ∈ completedGroups s g → record e ∈ HubSelector.allBlocks (births g))
    (hrecord : ∀ g, Set.InjOn record (completedGroups s g))
    (hdestination : ∀ g e, e ∈ completedGroups s g →
      (destination e).val = HubSelector.hubColour (rank g) (hinj g) (record e)) :
    ((reservedEvents (completedGroups s)).card : ℝ) ≤
      destinationEntropy destination s.entered.card / Real.log ((J : ℝ) / 2) := by
  have hs := run_valid actions (initial_valid free) hrun
  apply scale_group_count_le (completedGroups s) (completedGroups_disjoint hs) destination J hJ
    (fun i => (completedGroups_card hs hcomplete i).trans (hsize i)) births record rank hinj
    hvalid hrecord hdestination
  exact_mod_cast (by simpa using consumed_card_le_entered s)

end CompletedChronology

end SortingAdversary.Optimal.GroupReservations
