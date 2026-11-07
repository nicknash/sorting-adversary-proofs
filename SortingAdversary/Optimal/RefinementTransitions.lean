import SortingAdversary.Optimal.PinTransitions

/-!
# Endpoint palette refinements preserve the full local invariant

The old colour identities embed strictly increasingly into the refined
alphabet. Every old feasible assignment has its original-colour embedding in
the split system, so every old free coordinate remains nonconstant before the
new pin. The fresh endpoint colour is proved strictly interior, allowing the
checked interior-pin transition to finish the operation.
-/

namespace SortingAdversary.Optimal.RefinementTransitions

open WeakMaps WeakMaps.WeakSystem FiniteRefinement ControllerRouting PinTransitions

variable {α : Type*} [Fintype α] {K L : ℕ}

def mapPins (e : Fin (K + 1) → Fin (L + 1))
    (pins : α → Option (Fin (K + 1))) : α → Option (Fin (L + 1)) :=
  fun x => (pins x).map e

/-- Generic invariant transport through a concrete order-preserving palette
embedding. The required map-preservation premises are instantiated below. -/
theorem transport_invariant {S : WeakSystem α (K + 1)}
    {T : WeakSystem α (L + 1)} {pins : α → Option (Fin (K + 1))}
    (h : Invariant S pins) (e : Fin (K + 1) → Fin (L + 1)) (he : StrictMono e)
    (hedge : T.edge = S.edge)
    (hvalid : ∀ f, S.Valid f → T.Valid (fun x => e (f x)))
    (hpin : PinBounds T (mapPins e pins)) : Invariant T (mapPins e pins) := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  have hlo := hvalid _ (S.effectiveLower_valid h.closed hw)
  have hhi := hvalid _ (S.effectiveUpper_valid h.closed hw)
  refine ⟨?_, ?_, ⟨_, hlo⟩, ?_, ?_⟩
  · constructor
    · intro v
      simpa [hedge] using h.closed.refl v
    · intro u v w huv hvw
      rw [hedge] at *
      exact h.closed.trans u v w huv hvw
  · intro u v huv hvu
    rw [hedge] at *
    exact h.antisymm u v huv hvu
  · intro f hf x c hx
    exact valid_pin_value T _ hpin hf hx
  · intro x hx
    have hold : pins x = none := by
      cases hp : pins x with
      | none => rfl
      | some c => simp [mapPins, hp] at hx
    calc
      T.effectiveLower x ≤ e (S.effectiveLower x) := (T.valid_between_windows _ hlo x).1
      _ < e (S.effectiveUpper x) := he (h.free_window x hold)
      _ ≤ T.effectiveUpper x := (T.valid_between_windows _ hhi x).2

theorem embedColor_strictMono (c : Fin (K + 1)) : StrictMono (embedColor c) := by
  intro a b hab
  exact Refinement.embed_strictMono c.val hab

theorem embedColorBefore_strictMono (c : Fin (K + 1)) : StrictMono (embedColorBefore c) := by
  intro a b hab
  exact Refinement.embedBefore_strictMono c.val hab

omit [Fintype α] in
theorem embedded_valid {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (hp : PinBounds S pins)
    (c : Fin (K + 1)) {f : ColorMap α (K + 1)} (hf : S.Valid f) :
    (splitPalette S pins c).Valid (fun x => embedColor c (f x)) := by
  constructor
  · intro x
    cases hx : pins x with
    | none =>
        simp only [splitPalette, hx]
        constructor
        · exact (embedColor_strictMono c).monotone (hf.1 x).1
        · apply (upper_bound_iff c.val (S.upper x).val _).mpr
          simpa only [embedColor_val, Refinement.collapse_embed, Fin.le_def] using (hf.1 x).2
    | some d =>
        have heq := valid_pin_value S pins hp hf hx
        simp [splitPalette, hx, heq]
  · intro x y hxy
    exact (embedColor_strictMono c).monotone (hf.2 x y hxy)

omit [Fintype α] in
theorem embeddedBefore_valid {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (hp : PinBounds S pins)
    (c : Fin (K + 1)) {f : ColorMap α (K + 1)} (hf : S.Valid f) :
    (splitPaletteBefore S pins c).Valid (fun x => embedColorBefore c (f x)) := by
  constructor
  · intro x
    cases hx : pins x with
    | none =>
        simp only [splitPaletteBefore, hx]
        constructor
        · apply (lower_bound_iff c.val (S.lower x).val _).mpr
          simpa only [embedColorBefore_val, Refinement.collapse_embedBefore, Fin.le_def] using (hf.1 x).1
        · apply (upper_bound_iff c.val (S.upper x).val _).mpr
          simpa only [embedColorBefore_val, Refinement.collapse_embedBefore, Fin.le_def] using (hf.1 x).2
    | some d =>
        have heq := valid_pin_value S pins hp hf hx
        simp [splitPaletteBefore, hx, heq]
  · intro x y hxy
    exact (embedColorBefore_strictMono c).monotone (hf.2 x y hxy)

omit [Fintype α] in
theorem split_pin_bounds (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (c : Fin (K + 1)) :
    PinBounds (splitPalette S pins c) (mapPins (embedColor c) pins) := by
  intro x d hx
  cases hp : pins x with
  | none => simp [mapPins, hp] at hx
  | some e =>
      have heq : embedColor c e = d := by simpa [mapPins, hp] using hx
      simp [splitPalette, hp, heq]

omit [Fintype α] in
theorem splitBefore_pin_bounds (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (c : Fin (K + 1)) :
    PinBounds (splitPaletteBefore S pins c) (mapPins (embedColorBefore c) pins) := by
  intro x d hx
  cases hp : pins x with
  | none => simp [mapPins, hp] at hx
  | some e =>
      have heq : embedColorBefore c e = d := by simpa [mapPins, hp] using hx
      simp [splitPaletteBefore, hp, heq]

theorem split_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (c : Fin (K + 1)) :
    Invariant (splitPalette S pins c) (mapPins (embedColor c) pins) :=
  transport_invariant h _ (embedColor_strictMono c) rfl
    (fun _ hf => embedded_valid hp c hf) (split_pin_bounds S pins c)

theorem splitBefore_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (c : Fin (K + 1)) :
    Invariant (splitPaletteBefore S pins c) (mapPins (embedColorBefore c) pins) :=
  transport_invariant h _ (embedColorBefore_strictMono c) rfl
    (fun _ hf => embeddedBefore_valid hp c hf) (splitBefore_pin_bounds S pins c)

theorem lower_split_interior {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (v : α) (c : Fin (K + 1))
    (hl : S.effectiveLower v = c) (hu : c < S.effectiveUpper v) :
    (splitPalette S pins c).effectiveLower v < freshColor c ∧
      freshColor c < (splitPalette S pins c).effectiveUpper v := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  have hlo := embedded_valid hp c (S.effectiveLower_valid h.closed hw)
  have hhi := embedded_valid hp c (S.effectiveUpper_valid h.closed hw)
  constructor
  · apply lt_of_le_of_lt ((splitPalette S pins c).valid_between_windows _ hlo v).1
    rw [hl]
    change Refinement.embed c.val c.val < c.val + 1
    simp [Refinement.embed]
  · apply lt_of_lt_of_le _ ((splitPalette S pins c).valid_between_windows _ hhi v).2
    change c.val + 1 < Refinement.embed c.val (S.effectiveUpper v).val
    have hh : c.val < (S.effectiveUpper v).val := hu
    simp only [Refinement.embed, if_neg (not_le_of_gt hh)]
    omega

theorem upper_split_interior {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (v : α) (c : Fin (K + 1))
    (hl : S.effectiveLower v < c) (hu : S.effectiveUpper v = c) :
    (splitPaletteBefore S pins c).effectiveLower v < c.castSucc ∧
      c.castSucc < (splitPaletteBefore S pins c).effectiveUpper v := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  have hlo := embeddedBefore_valid hp c (S.effectiveLower_valid h.closed hw)
  have hhi := embeddedBefore_valid hp c (S.effectiveUpper_valid h.closed hw)
  constructor
  · apply lt_of_le_of_lt ((splitPaletteBefore S pins c).valid_between_windows _ hlo v).1
    change Refinement.embedBefore c.val (S.effectiveLower v).val < c.val
    have hh : (S.effectiveLower v).val < c.val := hl
    simp [Refinement.embedBefore, hh]
  · apply lt_of_lt_of_le _ ((splitPaletteBefore S pins c).valid_between_windows _ hhi v).2
    rw [hu]
    change c.val < Refinement.embedBefore c.val c.val
    simp [Refinement.embedBefore]

/-- A lower-endpoint split followed by its physical pin preserves the same
local invariant as an ordinary interior pin. -/
theorem lower_refinement_invariant [DecidableEq α] {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (v : α) (c : Fin (K + 1))
    (hl : S.effectiveLower v = c) (hu : c < S.effectiveUpper v) :
    Invariant (lowerRefinement S pins v c)
      (recordPin (mapPins (embedColor c) pins) v (freshColor c)) := by
  have hi := lower_split_interior h hp v c hl hu
  exact interior_pin_invariant (split_invariant h hp c) v (freshColor c) hi.1 hi.2

/-- The dual upper-endpoint transition is equally invariant preserving. -/
theorem upper_refinement_invariant [DecidableEq α] {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (v : α) (c : Fin (K + 1))
    (hl : S.effectiveLower v < c) (hu : S.effectiveUpper v = c) :
    Invariant (upperRefinement S pins v c)
      (recordPin (mapPins (embedColorBefore c) pins) v c.castSucc) := by
  have hi := upper_split_interior h hp v c hl hu
  exact interior_pin_invariant (splitBefore_invariant h hp c) v c.castSucc hi.1 hi.2

end SortingAdversary.Optimal.RefinementTransitions
