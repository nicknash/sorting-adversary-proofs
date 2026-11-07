import SortingAdversary.Optimal.LedgerRun

/-!
# Unique physical promotion locations in every accepted execution

The chronological action list has no repeated `(node identity, label)`
promotion. Acceptance requires a currently free location, while every
previous promotion remains recorded. This turns local extraction sublists
into globally unique event populations.
-/

namespace SortingAdversary.Optimal.LedgerPromotionTrace

open LedgerTreeBridge

variable {n : ℕ}

def promotedLocation : IncidenceLedger.Action n → Option (IncidenceLedger.Location n)
  | .promote location _ => some location
  | _ => none

def promotionLocations (actions : List (IncidenceLedger.Action n)) : List (IncidenceLedger.Location n) :=
  actions.filterMap promotedLocation

@[simp] theorem promotionLocations_append (first second : List (IncidenceLedger.Action n)) :
    promotionLocations (first ++ second) = promotionLocations first ++ promotionLocations second := by
  simp [promotionLocations]

theorem step_moved_mono {threshold : ℕ} {s t : IncidenceLedger.State n}
    (action : IncidenceLedger.Action n) (accepted : IncidenceLedger.step threshold s action = some t) :
    movedLocations s ⊆ movedLocations t := by
  cases action <;> simp only [IncidenceLedger.step] at accepted
  all_goals split at accepted
  all_goals try contradiction
  all_goals cases accepted
  all_goals simp only [movedLocations, Finset.image_insert]
  all_goals first | exact Finset.Subset.refl _ | exact Finset.subset_insert _ _

theorem run_moved_mono {threshold : ℕ} (actions : List (IncidenceLedger.Action n))
    {s t : IncidenceLedger.State n} (accepted : IncidenceLedger.run threshold s actions = some t) :
    movedLocations s ⊆ movedLocations t := by
  induction actions generalizing s with
  | nil =>
    cases accepted
    exact Finset.Subset.refl _
  | cons head tail ih =>
    simp only [IncidenceLedger.run] at accepted
    cases hs : IncidenceLedger.step threshold s head with
    | none => simp [hs] at accepted
    | some next =>
      simp only [hs, Option.bind_some] at accepted
      exact (step_moved_mono head hs).trans (ih accepted)

theorem step_promote_new {threshold : ℕ} {s t : IncidenceLedger.State n}
    (valid : IncidenceLedger.Valid threshold s) (location : IncidenceLedger.Location n)
    (kind : IncidenceLedger.Kind)
    (accepted : IncidenceLedger.step threshold s (.promote location kind) = some t) :
    location ∉ movedLocations s ∧ location ∈ movedLocations t := by
  simp only [IncidenceLedger.step] at accepted
  split at accepted
  next checks =>
    cases accepted
    constructor
    · intro hm
      obtain ⟨move, hmove, heq⟩ := Finset.mem_image.mp hm
      apply valid.move_not_free move hmove
      simpa only [heq] using checks.1
    · simp [movedLocations]
  next => contradiction

/-- The list of real emitted parent locations is unique and disjoint from
all moves recorded before this execution segment. -/
theorem accepted_promotions {threshold : ℕ} (actions : List (IncidenceLedger.Action n))
    {s t : IncidenceLedger.State n} (valid : IncidenceLedger.Valid threshold s)
    (accepted : IncidenceLedger.run threshold s actions = some t) :
    (promotionLocations actions).Nodup ∧
      ∀ location ∈ promotionLocations actions,
        location ∉ movedLocations s ∧ location ∈ movedLocations t := by
  induction actions generalizing s with
  | nil => simp [promotionLocations]
  | cons head tail ih =>
    simp only [IncidenceLedger.run] at accepted
    cases hs : IncidenceLedger.step threshold s head with
    | none => simp [hs] at accepted
    | some next =>
      simp only [hs, Option.bind_some] at accepted
      have ht := ih (IncidenceLedger.step_valid valid head hs) accepted
      have hmono := step_moved_mono head hs
      have htail : ∀ location ∈ promotionLocations tail,
          location ∉ movedLocations s ∧ location ∈ movedLocations t := by
        intro location hm
        exact ⟨fun h => (ht.2 location hm).1 (hmono h), (ht.2 location hm).2⟩
      cases head with
      | admit location =>
        simpa only [promotionLocations, List.filterMap_cons, promotedLocation] using And.intro ht.1 htail
      | physical row =>
        simpa only [promotionLocations, List.filterMap_cons, promotedLocation] using And.intro ht.1 htail
      | promote location kind =>
        have hnew := step_promote_new valid location kind hs
        change (location :: promotionLocations tail).Nodup ∧
          ∀ x ∈ location :: promotionLocations tail, x ∉ movedLocations s ∧ x ∈ movedLocations t
        refine ⟨List.nodup_cons.mpr ⟨?_, ht.1⟩, ?_⟩
        · intro hm
          exact (ht.2 location hm).1 hnew.2
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hnew.1, run_moved_mono tail accepted hnew.2⟩
          · exact htail x hx

theorem actual_promotion_locations_nodup (p : RecursiveController.Parameters) (N : ℕ)
    {final : ControllerMachine.Active p (N + 2)} {observations : History (N + 2)}
    (history : ControllerRun.ActiveRun p (ControllerMachine.initialActive p N) observations final) :
    (promotionLocations (LedgerRun.initialLog p N observations).actions).Nodup :=
  (accepted_promotions _ (IncidenceLedger.initial_valid _ _) (LedgerRun.initial_spec p N history).accepted).1

end SortingAdversary.Optimal.LedgerPromotionTrace
