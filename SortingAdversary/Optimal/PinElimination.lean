import SortingAdversary.Optimal.FiniteInsertion
import SortingAdversary.Optimal.FiniteRefinement
import SortingAdversary.Optimal.ControllerRouting

/-!
# Elimination of physical pins from numerical rows

The derived numerical system propagates all old unary bounds, then removes
every raw row incident to a physical pin. Pinned coordinates remain as
isolated singleton factors on the fixed label carrier. Consequently the
finite family of maps, every event probability, and every marginal are
unchanged. These propagated numerical lists are not the primitive public
walls to be lifted by a later palette refinement.
-/

namespace SortingAdversary.Optimal.PinElimination

open WeakMaps WeakMaps.WeakSystem SparseClosure FiniteRefinement
open FiniteInsertion ControllerRouting
open scoped BigOperators

variable {n K : ℕ}

/-- Remove pin-incident numerical rows after propagating their consequences. -/
def eliminatePins (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) : WeakSystem (Fin n) (K + 1) where
  edge u v := S.edge u v && decide (pins u = none ∧ pins v = none)
  lower := (closeSystem S).effectiveLower
  upper := (closeSystem S).effectiveUpper

@[simp] theorem edge_true (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (u v : Fin n) :
    (eliminatePins S pins).edge u v = true ↔
      S.edge u v = true ∧ pins u = none ∧ pins v = none := by
  simp [eliminatePins]

theorem pinned_outgoing (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) {u : Fin n} {c : Fin (K + 1)}
    (hu : pins u = some c) (v : Fin n) : (eliminatePins S pins).edge u v = false := by
  simp [eliminatePins, hu]

theorem pinned_incoming (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) {v : Fin n} {c : Fin (K + 1)}
    (hv : pins v = some c) (u : Fin n) : (eliminatePins S pins).edge u v = false := by
  simp [eliminatePins, hv]

theorem free_row (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) {u v : Fin n}
    (hu : pins u = none) (hv : pins v = none) :
    (eliminatePins S pins).edge u v = S.edge u v := by
  simp [eliminatePins, hu, hv]

/-- Even when the old system is infeasible, every retained numerical map
obeys the original primitive unary bounds. -/
theorem primitive_bounds (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) {f : ColorMap (Fin n) (K + 1)}
    (hf : (eliminatePins S pins).Valid f) (v : Fin n) :
    S.lower v ≤ f v ∧ f v ≤ S.upper v := by
  have hc := closeSystem_closed S
  exact ⟨((closeSystem S).lower_le_effectiveLower (hc.refl v)).trans (hf.1 v).1,
    (hf.1 v).2.trans ((closeSystem S).effectiveUpper_le_upper (hc.refl v))⟩

/-- Exact elimination: removed rows are recovered from their propagated
walls and the fixed pin values. No feasibility assumption is required. -/
theorem valid_iff (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (f : ColorMap (Fin n) (K + 1)) : (eliminatePins S pins).Valid f ↔ S.Valid f := by
  constructor
  · intro hf
    have hb := primitive_bounds S pins hf
    have hpin (x : Fin n) (c : Fin (K + 1)) (hx : pins x = some c) : f x = c := by
      obtain ⟨hl, hu⟩ := hp x c hx
      exact le_antisymm (hu ▸ (hb x).2) (hl ▸ (hb x).1)
    refine ⟨hb, ?_⟩
    intro u v huv
    have hclosed : (closeSystem S).edge u v = true := by
      change lookup (tableClosure S.edge) u v = true
      rw [lookup_tableClosure]
      exact closure_old S.edge huv
    cases hu : pins u with
    | some c =>
      calc
        f u = c := hpin u c hu
        _ = S.lower u := (hp u c hu).1.symm
        _ ≤ (closeSystem S).effectiveLower v :=
          (closeSystem S).lower_le_effectiveLower hclosed
        _ ≤ f v := (hf.1 v).1
    | none =>
      cases hv : pins v with
      | some c =>
        calc
          f u ≤ (closeSystem S).effectiveUpper u := (hf.1 u).2
          _ ≤ S.upper v := (closeSystem S).effectiveUpper_le_upper hclosed
          _ = c := (hp v c hv).2
          _ = f v := (hpin v c hv).symm
      | none => exact hf.2 u v ((edge_true _ _ _ _).mpr ⟨huv, hu, hv⟩)
  · intro hf
    have hf' := (propagateSystem_valid S f).mpr hf
    exact ⟨hf'.1, fun u v huv => hf.2 u v ((edge_true _ _ _ _).mp huv).1⟩

theorem maps_eq (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins) :
    (eliminatePins S pins).maps = S.maps := by
  ext f
  simp only [mem_maps, valid_iff S pins hp]

theorem count_eq (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins) :
    (eliminatePins S pins).count = S.count := by
  simp only [count, maps_eq S pins hp]

theorem fiber_eq (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (v : Fin n) (c : Fin (K + 1)) :
    (eliminatePins S pins).fiber v c = S.fiber v c := by
  simp only [fiber, maps_eq S pins hp]

/-- Equality of the actual finite event laws, including degenerate empty laws. -/
theorem event_probability_eq (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (P : ColorMap (Fin n) (K + 1) → Prop) [DecidablePred P] :
    (((eliminatePins S pins).maps.filter P).card : ℚ) / (eliminatePins S pins).count =
      ((S.maps.filter P).card : ℚ) / S.count := by
  rw [maps_eq S pins hp, count_eq S pins hp]

/-- Uniform finite expectations used by the coupling are unchanged. -/
theorem mean_eq (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (φ : ColorMap (Fin n) (K + 1) → ℚ) :
    FiniteProbability.mean (fun f : SystematicCoupling.State (eliminatePins S pins) => φ f.val) =
      FiniteProbability.mean (fun f : SystematicCoupling.State S => φ f.val) := by
  unfold FiniteProbability.mean
  rw [ClockStationarity.sum_states, ClockStationarity.sum_states,
    ClockStationarity.card_states, ClockStationarity.card_states,
    maps_eq S pins hp, count_eq S pins hp]

/-- Effective endpoints are semantic extrema of a feasible closed weak-map
family; two representations of the same family have the same endpoints. -/
theorem windows_eq_of_valid_iff {α : Type*} [Fintype α]
    (S T : WeakSystem α (K + 1)) (hS : S.Closed) (hT : T.Closed)
    (hne : ∃ f, S.Valid f) (heq : ∀ f, T.Valid f ↔ S.Valid f) (v : α) :
    T.effectiveLower v = S.effectiveLower v ∧ T.effectiveUpper v = S.effectiveUpper v := by
  have hneT : ∃ f, T.Valid f := by obtain ⟨f, hf⟩ := hne; exact ⟨f, (heq f).mpr hf⟩
  have hSL := S.effectiveLower_valid hS ((S.feasible_iff_windows hS).mp hne)
  have hSU := S.effectiveUpper_valid hS ((S.feasible_iff_windows hS).mp hne)
  have hTL := T.effectiveLower_valid hT ((T.feasible_iff_windows hT).mp hneT)
  have hTU := T.effectiveUpper_valid hT ((T.feasible_iff_windows hT).mp hneT)
  exact ⟨le_antisymm (T.valid_between_windows _ ((heq _).mpr hSL) v).1
      (S.valid_between_windows _ ((heq _).mp hTL) v).1,
    le_antisymm (S.valid_between_windows _ ((heq _).mp hTU) v).2
      (T.valid_between_windows _ ((heq _).mpr hSU) v).2⟩

theorem windows_eq (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (hne : ∃ f, S.Valid f) (v : Fin n) :
    (closeSystem (eliminatePins S pins)).effectiveLower v = (closeSystem S).effectiveLower v ∧
      (closeSystem (eliminatePins S pins)).effectiveUpper v = (closeSystem S).effectiveUpper v := by
  apply windows_eq_of_valid_iff _ _ (closeSystem_closed S) (closeSystem_closed _)
  · obtain ⟨f, hf⟩ := hne
    exact ⟨f, (closeSystem_valid S f).mpr hf⟩
  · intro f
    simp only [closeSystem_valid, valid_iff S pins hp]

/-- Feasible physical pins remain singleton factors after elimination. -/
theorem pinBounds (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (hne : ∃ f, S.Valid f) : PinBounds (eliminatePins S pins) pins := by
  obtain ⟨f, hf⟩ := hne
  have hf' : (closeSystem S).Valid f := (closeSystem_valid S f).mpr hf
  have hc := closeSystem_closed S
  intro x c hx
  obtain ⟨hl, hu⟩ := hp x c hx
  have hfc := valid_pin_value S pins hp hf hx
  have hw := (closeSystem S).valid_between_windows f hf' x
  have hlo := (closeSystem S).lower_le_effectiveLower (hc.refl x)
  have hhi := (closeSystem S).effectiveUpper_le_upper (hc.refl x)
  change S.lower x ≤ _ at hlo
  change _ ≤ S.upper x at hhi
  rw [hl] at hlo
  rw [hu] at hhi
  rw [hfc] at hw
  exact ⟨le_antisymm hw.1 hlo, le_antisymm hhi hw.2⟩

/-- Numerical closure remains a suborder of any old public closed order. -/
theorem closed_row_old (C : OrderedSystem n K)
    (pins : Fin n → Option (Fin (K + 1))) {u v : Fin n}
    (huv : (closeSystem (eliminatePins C.system pins)).edge u v = true) :
    C.system.edge u v = true := by
  have hr : Respects (closure (eliminatePins C.system pins).edge)
      (fun x => (Label.mk x : Label C)) :=
    (respects_closure _ _).mpr (fun x y hxy => ((edge_true _ _ _ _).mp hxy).1)
  apply hr u v
  simpa only [closeSystem, lookup_tableClosure] using huv

/-- The numerical invariant is retained; the public closed relation itself
continues to live in the original primitive-wall state. -/
theorem invariant {S : WeakSystem (Fin n) (K + 1)}
    {pins : Fin n → Option (Fin (K + 1))} (h : Invariant S pins) (hp : PinBounds S pins) :
    Invariant (closeSystem (eliminatePins S pins)) pins := by
  let C : OrderedSystem n K := ⟨S, h.closed, h.antisymm⟩
  have heq (f : ColorMap (Fin n) (K + 1)) :
      (closeSystem (eliminatePins S pins)).Valid f ↔ S.Valid f := by
    simp only [closeSystem_valid, valid_iff S pins hp]
  refine ⟨closeSystem_closed _, ?_, ?_, ?_, ?_⟩
  · intro u v huv hvu
    exact h.antisymm u v (closed_row_old C pins huv) (closed_row_old C pins hvu)
  · obtain ⟨f, hf⟩ := h.feasible
    exact ⟨f, (heq f).mpr hf⟩
  · intro f hf
    exact h.pins_valid f ((heq f).mp hf)
  · intro v hv
    have hw := windows_eq_of_valid_iff S _ h.closed (closeSystem_closed _)
      h.feasible heq v
    rw [hw.1, hw.2]
    exact h.free_window v hv

end SortingAdversary.Optimal.PinElimination
