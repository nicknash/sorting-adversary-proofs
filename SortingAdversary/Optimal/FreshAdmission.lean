import SortingAdversary.Optimal.RefinementTransitions
import Mathlib.Data.Fintype.Prod

/-!
# Fresh admissions on a fixed global label carrier

An unused label is stored as an isolated, fixed dummy coordinate. Admitting it
replaces that singleton list with the full palette. This representation avoids
renumbering every old label when a child grows. The resulting weak-map space
is proved equivalent to the old space times the current palette, and the full
local invariant is preserved. Dummy coordinates are not physical child members.
-/

namespace SortingAdversary.Optimal.FreshAdmission

open WeakMaps WeakMaps.WeakSystem FiniteRefinement ControllerRouting
open PinTransitions RefinementTransitions

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

structure Unused (S : WeakSystem α (K + 1)) (v : α) (d : Fin (K + 1)) : Prop where
  lower : S.lower v = d
  upper : S.upper v = d
  outgoing : ∀ x, S.edge v x = true → x = v
  incoming : ∀ x, S.edge x v = true → x = v

def admit (S : WeakSystem α (K + 1)) (v : α) : WeakSystem α (K + 1) where
  edge := S.edge
  lower x := if x = v then 0 else S.lower x
  upper x := if x = v then Fin.last K else S.upper x

def unpin (pins : α → Option (Fin (K + 1))) (v : α) : α → Option (Fin (K + 1)) :=
  Function.update pins v none

omit [Fintype α] [DecidableEq α] in
theorem unused_value {S : WeakSystem α (K + 1)} {v : α} {d : Fin (K + 1)}
    (h : Unused S v d) {f : ColorMap α (K + 1)} (hf : S.Valid f) : f v = d := by
  have hv := hf.1 v
  rw [h.lower, h.upper] at hv
  exact le_antisymm hv.2 hv.1

omit [Fintype α] in
theorem admit_update_valid {S : WeakSystem α (K + 1)} {v : α} {d : Fin (K + 1)}
    (h : Unused S v d) {f : ColorMap α (K + 1)} (hf : S.Valid f) (c : Fin (K + 1)) :
    (admit S v).Valid (Function.update f v c) := by
  constructor
  · intro x
    by_cases hx : x = v
    · subst x
      simp [admit, Fin.le_last]
    · simpa [admit, hx] using hf.1 x
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy := h.outgoing y hxy
      subst y
      exact le_rfl
    · by_cases hy : y = v
      · subst y
        exact (hx (h.incoming x hxy)).elim
      · simpa [hx, hy] using hf.2 x y hxy

omit [Fintype α] in
theorem retract_valid {S : WeakSystem α (K + 1)} {v : α} {d : Fin (K + 1)}
    (h : Unused S v d) {g : ColorMap α (K + 1)} (hg : (admit S v).Valid g) :
    S.Valid (Function.update g v d) := by
  constructor
  · intro x
    by_cases hx : x = v
    · subst x
      simp [h.lower, h.upper]
    · simpa [admit, hx] using hg.1 x
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy := h.outgoing y hxy
      subst y
      exact le_rfl
    · by_cases hy : y = v
      · subst y
        exact (hx (h.incoming x hxy)).elim
      · simpa [hx, hy] using hg.2 x y hxy

/-- Actual finite-map bijection underlying a child birth. -/
def admissionEquiv {S : WeakSystem α (K + 1)} {v : α} {d : Fin (K + 1)}
    (h : Unused S v d) :
    ({f : ColorMap α (K + 1) // S.Valid f} × Fin (K + 1)) ≃
      {g : ColorMap α (K + 1) // (admit S v).Valid g} where
  toFun p := ⟨Function.update p.1.val v p.2, admit_update_valid h p.1.property p.2⟩
  invFun g := (⟨Function.update g.val v d, retract_valid h g.property⟩, g.val v)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      by_cases hx : x = v
      · subst x
        simp [unused_value h p.1.property]
      · simp [hx]
    · simp
  right_inv g := by
    apply Subtype.ext
    funext x
    by_cases hx : x = v
    · subst x
      simp
    · simp [hx]

theorem admission_count {S : WeakSystem α (K + 1)} {v : α} {d : Fin (K + 1)}
    (h : Unused S v d) : (admit S v).count = S.count * (K + 1) := by
  have hc := Fintype.card_congr (admissionEquiv h)
  simpa [Fintype.card_prod, Fintype.card_subtype, count, maps] using hc.symm

theorem admission_credit {S : WeakSystem α (K + 1)} {v : α} {d : Fin (K + 1)}
    (h : Unused S v d) {j : ℕ} (hj : j ≤ K + 1) :
    j * S.count ≤ (admit S v).count := by
  rw [admission_count h, Nat.mul_comm S.count]
  exact Nat.mul_le_mul_right S.count hj

/-- A fresh admission preserves every old free coordinate's two witnesses;
the new coordinate has the palette's two distinct endpoints. -/
theorem admission_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (hi : Invariant S pins)
    {v : α} {d : Fin (K + 1)} (hu : Unused S v d) (hK : 0 < K) :
    Invariant (admit S v) (unpin pins v) := by
  have hw := (S.feasible_iff_windows hi.closed).mp hi.feasible
  have hlo := admit_update_valid hu (S.effectiveLower_valid hi.closed hw) (0 : Fin (K + 1))
  have hhi := admit_update_valid hu (S.effectiveUpper_valid hi.closed hw) (Fin.last K)
  refine ⟨⟨hi.closed.refl, hi.closed.trans⟩, hi.antisymm, ⟨_, hlo⟩, ?_, ?_⟩
  · intro g hg x c hx
    have hxv : x ≠ v := by
      rintro rfl
      simp [unpin] at hx
    have hp : pins x = some c := by simpa [unpin, hxv] using hx
    have hr := retract_valid hu hg
    have heq := hi.pins_valid _ hr x c hp
    simpa [hxv] using heq
  · intro x hx
    have hlower := ((admit S v).valid_between_windows _ hlo x).1
    have hupper := ((admit S v).valid_between_windows _ hhi x).2
    by_cases hxv : x = v
    · subst x
      simp only [Function.update_self] at hlower hupper
      exact hlower.trans_lt ((show (0 : Fin (K + 1)) < Fin.last K from hK).trans_le hupper)
    · have hp : pins x = none := by simpa [unpin, hxv] using hx
      simp only [Function.update_of_ne hxv] at hlower hupper
      exact hlower.trans_lt ((hi.free_window x hp).trans_le hupper)

omit [Fintype α] in
theorem admission_pin_bounds {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (hp : PinBounds S pins) (v : α) :
    PinBounds (admit S v) (unpin pins v) := by
  intro x c hx
  have hxv : x ≠ v := by
    rintro rfl
    simp [unpin] at hx
  have hh : pins x = some c := by simpa [unpin, hxv] using hx
  simpa [admit, hxv] using hp x c hh

omit [Fintype α] [DecidableEq α] in
theorem enlargement_pin_bounds {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (hp : PinBounds S pins) :
    PinBounds S.enlarge (mapPins Fin.castSucc pins) := by
  intro x c hx
  cases hpx : pins x with
  | none => simp [mapPins, hpx] at hx
  | some d =>
      have hc : d.castSucc = c := by simpa [mapPins, hpx] using hx
      obtain ⟨hl, hu⟩ := hp x d hpx
      simp [enlarge, hl, hu, hc]

omit [DecidableEq α] in
/-- Appending a top colour does not enlarge any old list or change the old
law, and preserves the full local invariant with old identities embedded. -/
theorem enlargement_invariant {S : WeakSystem α (K + 1)}
    {pins : α → Option (Fin (K + 1))} (hi : Invariant S pins) (hp : PinBounds S pins) :
    Invariant S.enlarge (mapPins Fin.castSucc pins) := by
  apply transport_invariant hi Fin.castSucc (fun _ _ h => h) rfl
  · intro f hf
    exact (valid_enlarge_embedding S f).mpr hf
  · exact enlargement_pin_bounds hp

end SortingAdversary.Optimal.FreshAdmission
