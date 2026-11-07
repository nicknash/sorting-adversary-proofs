import SortingAdversary.Optimal.MeasuredPin

/-! Align a measured pin built from computed coordinates with a reference
pin used only in erased certificates. The reference pin is never queried for
an executable vertex, colour or charge. -/

namespace SortingAdversary.Optimal.MeasuredPinAs

open PrimitiveWork WidthRepair RepresentationWork

variable {n : ℕ} {s : State n}

theorem free_of_equal (expected : PinUpdate s) (v : Fin n) (hv : v = expected.vertex) :
    s.pool.pins v = none := by rw [hv]; exact expected.free

theorem supported_of_equal (expected : PinUpdate s) (v : Fin n) (hv : v = expected.vertex)
    (c : Fin (s.pool.palette + 1)) (hc : c = expected.colour) :
    s.pool.system.effectiveLower v ≤ c ∧ c ≤ s.pool.system.effectiveUpper v := by
  rw [hv, hc]
  exact expected.supported

theorem retained_of_equal (expected : PinUpdate s) (v : Fin n) (hv : v = expected.vertex)
    (c : Fin (s.pool.palette + 1)) (hc : c = expected.colour) (charge : ℚ) (hcharge : charge = expected.charge) :
    (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds v
        (free_of_equal expected v hv) c (supported_of_equal expected v hv c hc)).system.count := by
  subst v
  subst c
  subst charge
  have h := expected.retained
  rw [expected.actual] at h
  exact h

def pin (a : LocalAccess s) (expected : PinUpdate s) (v : Fin n) (hv : v = expected.vertex)
    (c : Fin (s.pool.palette + 1)) (hc : c = expected.colour) (charge : ℚ) (hcharge : charge = expected.charge) :
    Result (MeasuredPin.Output expected) :=
  let chosen := MeasuredPin.pin a v (free_of_equal expected v hv) c
    (supported_of_equal expected v hv c hc) (by rw [hv]; exact expected.mate) charge
    (retained_of_equal expected v hv c hc charge hcharge)
  ⟨⟨chosen.value.update, chosen.value.access,
    chosen.value.exact.trans (MeasuredPin.update_ext _ _ hv hc hcharge), chosen.value.bounded⟩, chosen.work⟩

theorem pin_work_le (a : LocalAccess s) {A : ℕ} (h : AccessBound a A)
    (expected : PinUpdate s) (v : Fin n) (hv : v = expected.vertex)
    (c : Fin (s.pool.palette + 1)) (hc : c = expected.colour) (charge : ℚ) (hcharge : charge = expected.charge) :
    (pin a expected v hv c hc charge hcharge).work ≤ MeasuredPin.workBound n s.pool.palette A :=
  MeasuredPin.pin_work_le a h v _ c _ _ charge _

end SortingAdversary.Optimal.MeasuredPinAs
