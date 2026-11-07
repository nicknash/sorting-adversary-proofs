import SortingAdversary.Optimal.ControllerRouting
import SortingAdversary.Optimal.FiniteRefinement

/-!
# Interior pins preserve the controller invariant

All formulas are for the primitive `pinAt` operation, which intersects a
single original list with its physical pin. Effective windows are recomputed;
they are never stored as artificial walls. This distinction matters after a
later palette refinement.
-/

namespace SortingAdversary.Optimal.PinTransitions

open WeakMaps WeakMaps.WeakSystem FiniteRefinement ControllerRouting

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

theorem pinAt_lower (S : WeakSystem α (K + 1)) (v x : α) (c : Fin (K + 1)) :
    (pinAt S v c).effectiveLower x =
      if S.edge v x = true then max (S.effectiveLower x) c else S.effectiveLower x := by
  have hold : S.effectiveLower x ≤ (pinAt S v c).effectiveLower x := by
    apply Finset.sup_le
    intro u _
    split_ifs with hux
    · apply le_trans _ ((pinAt S v c).lower_le_effectiveLower hux)
      by_cases huv : u = v
      · simp [pinAt, huv]
      · simp [pinAt, huv]
    · exact bot_le
  by_cases hvx : S.edge v x = true
  · rw [if_pos hvx]
    apply le_antisymm
    · apply Finset.sup_le
      intro u _
      split_ifs with hux
      · have hux' : S.edge u x = true := hux
        by_cases huv : u = v
        · subst u
          simpa [pinAt] using max_le_max_right c (S.lower_le_effectiveLower hux')
        · simpa [pinAt, huv] using
            (S.lower_le_effectiveLower hux').trans (le_max_left (S.effectiveLower x) c)
      · exact bot_le
    · apply max_le hold
      have h := (pinAt S v c).lower_le_effectiveLower (u := v) (v := x) hvx
      exact (le_max_right (S.lower v) c).trans (by simpa [pinAt] using h)
  · rw [if_neg hvx]
    apply le_antisymm _ hold
    apply Finset.sup_le
    intro u _
    split_ifs with hux
    · have hux' : S.edge u x = true := hux
      have huv : u ≠ v := by rintro rfl; exact hvx hux'
      simpa [pinAt, huv] using S.lower_le_effectiveLower hux'
    · exact bot_le

theorem pinAt_upper (S : WeakSystem α (K + 1)) (v x : α) (c : Fin (K + 1)) :
    (pinAt S v c).effectiveUpper x =
      if S.edge x v = true then min (S.effectiveUpper x) c else S.effectiveUpper x := by
  have hold : (pinAt S v c).effectiveUpper x ≤ S.effectiveUpper x := by
    apply Finset.le_inf
    intro u _
    split_ifs with hxu
    · apply le_trans ((pinAt S v c).effectiveUpper_le_upper hxu)
      by_cases huv : u = v
      · simp [pinAt, huv]
      · simp [pinAt, huv]
    · exact le_top
  by_cases hxv : S.edge x v = true
  · rw [if_pos hxv]
    apply le_antisymm
    · apply le_min hold
      have h := (pinAt S v c).effectiveUpper_le_upper (u := x) (v := v) hxv
      exact (show (pinAt S v c).effectiveUpper x ≤ min (S.upper v) c by
        simpa [pinAt] using h).trans (min_le_right _ _)
    · apply Finset.le_inf
      intro u _
      split_ifs with hxu
      · have hxu' : S.edge x u = true := hxu
        by_cases huv : u = v
        · subst u
          simpa [pinAt] using min_le_min_right c (S.effectiveUpper_le_upper hxu')
        · simpa [pinAt, huv] using
            (min_le_left (S.effectiveUpper x) c).trans (S.effectiveUpper_le_upper hxu')
      · exact le_top
  · rw [if_neg hxv]
    apply le_antisymm hold
    apply Finset.le_inf
    intro u _
    split_ifs with hxu
    · have hxu' : S.edge x u = true := hxu
      have huv : u ≠ v := by rintro rfl; exact hxv hxu'
      simpa [pinAt, huv] using S.effectiveUpper_le_upper hxu'
    · exact le_top

/-- A newly pinned label leaves the free set. Existing pins retain exactly
their identities. -/
def recordPin (pins : α → Option (Fin (K + 1))) (v : α) (c : Fin (K + 1)) :
    α → Option (Fin (K + 1)) := Function.update pins v (some c)

omit [Fintype α] in
@[simp] theorem recordPin_self (pins : α → Option (Fin (K + 1)))
    (v : α) (c : Fin (K + 1)) : recordPin pins v c v = some c := by
  simp [recordPin]

omit [Fintype α] in
theorem recordPin_none {pins : α → Option (Fin (K + 1))} {v x : α} {c : Fin (K + 1)}
    (h : recordPin pins v c x = none) : x ≠ v ∧ pins x = none := by
  by_cases hx : x = v
  · subst x
    simp at h
  · exact ⟨hx, by simpa [recordPin, hx] using h⟩

/-- Strict interiority prevents any other free coordinate becoming a singleton. -/
theorem interior_pin_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) (v : α) (c : Fin (K + 1))
    (hl : S.effectiveLower v < c) (hu : c < S.effectiveUpper v) :
    Invariant (pinAt S v c) (recordPin pins v c) := by
  have hclosed : (pinAt S v c).Closed := ⟨h.closed.refl, h.closed.trans⟩
  have hfeas : ∃ f, (pinAt S v c).Valid f := by
    obtain ⟨f, hf, heq⟩ := (S.support_iff_window h.closed h.feasible v c).mpr ⟨hl.le, hu.le⟩
    exact ⟨f, (valid_pinAt S v c f).mpr ⟨hf, heq⟩⟩
  refine ⟨hclosed, h.antisymm, hfeas, ?_, ?_⟩
  · intro f hf x d hx
    obtain ⟨hf, heq⟩ := (valid_pinAt S v c f).mp hf
    by_cases hxv : x = v
    · subst x
      have hcd : c = d := by simpa using hx
      exact heq.trans hcd
    · have hpin : pins x = some d := by simpa [recordPin, hxv] using hx
      exact h.pins_valid f hf x d hpin
  · intro x hx
    obtain ⟨hxv, hnone⟩ := recordPin_none hx
    have hfree := h.free_window x hnone
    rw [pinAt_lower, pinAt_upper]
    by_cases hvx : S.edge v x = true
    · have hxv' : S.edge x v ≠ true := fun h' => hxv (h.antisymm x v h' hvx)
      rw [if_pos hvx, if_neg hxv']
      exact max_lt hfree (hu.trans_le (S.effectiveUpper_mono h.closed hvx))
    · rw [if_neg hvx]
      by_cases hxv' : S.edge x v = true
      · rw [if_pos hxv']
        exact lt_min hfree ((S.effectiveLower_mono h.closed hxv').trans_lt hl)
      · rw [if_neg hxv']
        exact hfree

omit [DecidableEq α] in
/-- Interior admission cannot import any old strict comparison to an older
member of the selected child. -/
theorem interior_birth_independent {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins) {v p : α} {c : Fin (K + 1)}
    (hp : pins p = some c) (hl : S.effectiveLower v < c) (hu : c < S.effectiveUpper v) :
    S.edge p v ≠ true ∧ S.edge v p ≠ true := by
  have hw := (S.feasible_iff_windows h.closed).mp h.feasible
  have hf := S.effectiveLower_valid h.closed hw
  have hg := S.effectiveUpper_valid h.closed hw
  exact Routing.interior_pin_incomparable hf.2 hg.2
    (h.pins_valid _ hf) (h.pins_valid _ hg) hp hl hu

/-- The primitive physical-singleton representation survives an interior pin. -/
theorem pin_bounds_preserved {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (h : Invariant S pins)
    (hp : PinBounds S pins) (v : α) (c : Fin (K + 1))
    (hl : S.effectiveLower v ≤ c) (hu : c ≤ S.effectiveUpper v) :
    PinBounds (pinAt S v c) (recordPin pins v c) := by
  intro x d hx
  by_cases hxv : x = v
  · subst x
    have hcd : c = d := by simpa using hx
    subst d
    have hlow : S.lower v ≤ c := (S.lower_le_effectiveLower (h.closed.refl v)).trans hl
    have hupp : c ≤ S.upper v := hu.trans (S.effectiveUpper_le_upper (h.closed.refl v))
    simp [pinAt, max_eq_right hlow, min_eq_right hupp]
  · have hp' : pins x = some d := by simpa [recordPin, hxv] using hx
    simpa [pinAt, hxv] using hp x d hp'

end SortingAdversary.Optimal.PinTransitions
