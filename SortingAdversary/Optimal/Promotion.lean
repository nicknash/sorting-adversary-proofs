import SortingAdversary.Optimal.FreshAdmission
import SortingAdversary.Optimal.MarginalCalibration

/-!+# One executable parent promotion

The selected colour is accepted anywhere in the effective support. The
procedure determines whether it is interior, the lower endpoint, or the
upper endpoint, and performs the corresponding checked transition. Its
returned certificate includes the actual parent count, the immutable-colour
embedding, preservation of every other physical pin, and independence from
the destination's old child members. No refinement case is left to a caller.
-/

namespace SortingAdversary.Optimal.Promotion

open WeakMaps WeakMaps.WeakSystem FiniteRefinement ControllerRouting
open PinTransitions RefinementTransitions

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- Data and proved postconditions of an actual promotion at the parent. -/
structure Result (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (v : α) (c : Fin (K + 1)) where
  palette : ℕ
  system : WeakSystem α (palette + 1)
  newPins : α → Option (Fin (palette + 1))
  embed : Fin (K + 1) → Fin (palette + 1)
  destination : Fin (palette + 1)
  embed_strict : StrictMono embed
  palette_bounds : K ≤ palette ∧ palette ≤ K + 1
  invariant : Invariant system newPins
  pin_bounds : PinBounds system newPins
  edges : system.edge = S.edge
  pins_eq : newPins = recordPin (mapPins embed pins) v destination
  retains_fiber : (S.fiber v c).card ≤ system.count
  independent : ∀ p d, pins p = some d → embed d = destination →
    S.edge p v ≠ true ∧ S.edge v p ≠ true

theorem freshColor_ne_embed (c d : Fin (K + 1)) : freshColor c ≠ embedColor c d := by
  intro heq
  have hh := congrArg Fin.val heq
  simp only [freshColor_val, embedColor_val, Refinement.embed] at hh
  split_ifs at hh <;> omega

theorem beforeColor_ne_embed (c d : Fin (K + 1)) : c.castSucc ≠ embedColorBefore c d := by
  intro heq
  have hh := congrArg Fin.val heq
  simp only [Fin.val_castSucc, embedColorBefore_val, Refinement.embedBefore] at hh
  split_ifs at hh <;> omega

/-- The one-colour operation, including both endpoint refinements. -/
def promote (S : WeakSystem α (K + 1)) (pins : α → Option (Fin (K + 1)))
    (h : Invariant S pins) (hp : PinBounds S pins)
    (v : α) (hv : pins v = none) (c : Fin (K + 1))
    (hc : S.effectiveLower v ≤ c ∧ c ≤ S.effectiveUpper v) : Result S pins v c :=
  if hl : S.effectiveLower v = c then
    let hi := lower_split_interior h hp v c hl (hl ▸ h.free_window v hv)
    let hs := split_invariant h hp c
    { palette := K + 1
      system := lowerRefinement S pins v c
      newPins := recordPin (mapPins (embedColor c) pins) v (freshColor c)
      embed := embedColor c
      destination := freshColor c
      embed_strict := embedColor_strictMono c
      palette_bounds := ⟨Nat.le_succ K, le_rfl⟩
      invariant := lower_refinement_invariant h hp v c hl (hl ▸ h.free_window v hv)
      pin_bounds := pin_bounds_preserved hs (split_pin_bounds S pins c) v (freshColor c) hi.1.le hi.2.le
      edges := rfl
      pins_eq := rfl
      retains_fiber := lower_refinement_count S h.closed pins hp v c S.effectiveUpper
        (S.effectiveUpper_valid h.closed ((S.feasible_iff_windows h.closed).mp h.feasible))
        (hl ▸ h.free_window v hv)
      independent := fun _ d _ hd => False.elim (freshColor_ne_embed c d hd.symm) }
  else if hu : S.effectiveUpper v = c then
    have hlt : S.effectiveLower v < c := hu ▸ h.free_window v hv
    let hi := upper_split_interior h hp v c hlt hu
    let hs := splitBefore_invariant h hp c
    { palette := K + 1
      system := upperRefinement S pins v c
      newPins := recordPin (mapPins (embedColorBefore c) pins) v c.castSucc
      embed := embedColorBefore c
      destination := c.castSucc
      embed_strict := embedColorBefore_strictMono c
      palette_bounds := ⟨Nat.le_succ K, le_rfl⟩
      invariant := upper_refinement_invariant h hp v c hlt hu
      pin_bounds := pin_bounds_preserved hs (splitBefore_pin_bounds S pins c) v c.castSucc hi.1.le hi.2.le
      edges := rfl
      pins_eq := rfl
      retains_fiber := upper_refinement_count S h.closed pins hp v c S.effectiveLower
        (S.effectiveLower_valid h.closed ((S.feasible_iff_windows h.closed).mp h.feasible)) hlt
      independent := fun _ d _ hd => False.elim (beforeColor_ne_embed c d hd.symm) }
  else
    have hlt : S.effectiveLower v < c := lt_of_le_of_ne hc.1 hl
    have hut : c < S.effectiveUpper v := lt_of_le_of_ne hc.2 (Ne.symm hu)
    { palette := K
      system := pinAt S v c
      newPins := recordPin pins v c
      embed := id
      destination := c
      embed_strict := fun _ _ hh => hh
      palette_bounds := ⟨le_rfl, Nat.le_succ K⟩
      invariant := interior_pin_invariant h v c hlt hut
      pin_bounds := pin_bounds_preserved h hp v c hc.1 hc.2
      edges := rfl
      pins_eq := by
        have heq : mapPins id pins = pins := by
          funext x
          unfold mapPins
          cases pins x <;> rfl
        rw [heq]
      retains_fiber := by simp only [count, maps_pinAt]; exact le_rfl
      independent := by
        intro p d hd hdc
        change d = c at hdc
        subst d
        exact interior_birth_independent h hd hlt hut }

@[simp] theorem promoted_pin (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (v : α) (c : Fin (K + 1))
    (r : Result S pins v c) : r.newPins v = some r.destination := by
  rw [r.pins_eq]
  simp [recordPin]

theorem other_pin (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (v : α) (c : Fin (K + 1))
    (r : Result S pins v c) {x : α} (hx : x ≠ v) :
    r.newPins x = (pins x).map r.embed := by
  rw [r.pins_eq]
  simp [recordPin, mapPins, hx]

/-- An old free label other than the moved one is still free. -/
theorem free_preserved (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (v : α) (c : Fin (K + 1))
    (r : Result S pins v c) {x : α} (hx : x ≠ v) :
    r.newPins x = none ↔ pins x = none := by
  rw [other_pin S pins v c r hx]
  cases pins x <;> simp

/-- Every denominator-free fibre price survives the actual endpoint choice. -/
theorem price_preserved (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (v : α) (c : Fin (K + 1))
    (r : Result S pins v c) (A : ℕ)
    (hA : S.count ≤ A * (S.fiber v c).card) : S.count ≤ A * r.system.count :=
  hA.trans (Nat.mul_le_mul_left A r.retains_fiber)

/-- The calibrated ordinary choice has its claimed true parent retention,
including both cases requiring a fresh endpoint colour. -/
theorem ordinary_price (S : WeakSystem α (K + 1))
    (pins : α → Option (Fin (K + 1))) (h : Invariant S pins) (hp : PinBounds S pins)
    (v : α) (hv : pins v = none)
    (q : Fin (K + 1) → ℚ)
    (herr : ∀ i, |q i - MarginalCalibration.cdf S v (i.val + 1)| ≤ (1 / 16 : ℚ))
    (c : Fin (K + 1))
    (hcl : (MarginalCalibration.selectedInterval S v (S.count_pos_iff.mpr h.feasible) q herr).1 ≤ c)
    (hcu : c ≤ (MarginalCalibration.selectedInterval S v (S.count_pos_iff.mpr h.feasible) q herr).2)
    (hc : S.effectiveLower v ≤ c ∧ c ≤ S.effectiveUpper v) :
    S.count ≤ 16 *
      ((MarginalCalibration.selectedInterval S v (S.count_pos_iff.mpr h.feasible) q herr).2.val + 1 -
        (MarginalCalibration.selectedInterval S v (S.count_pos_iff.mpr h.feasible) q herr).1.val) *
      (promote S pins h hp v hv c hc).system.count := by
  exact price_preserved S pins v c (promote S pins h hp v hv c hc) _
    (MarginalCalibration.selected_parent_fiber_count S v (S.count_pos_iff.mpr h.feasible) q herr c hcl hcu)

end SortingAdversary.Optimal.Promotion
