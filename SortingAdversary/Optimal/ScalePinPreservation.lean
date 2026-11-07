import SortingAdversary.Optimal.ScaleGeometry
import SortingAdversary.Optimal.PinElimination

/-!
# Reserved scale labels survive earlier physical pins

This combines the actual primitive pin, exact elimination of its numerical
rows, and sparse graph separation. Both effective endpoints and an existing
free incident row at another reserved label are preserved.
-/

namespace SortingAdversary.Optimal.ScalePinPreservation

open WeakMaps WeakMaps.WeakSystem SparseClosure FiniteRefinement PinTransitions
open ControllerRouting PinElimination ScaleGeometry GraphBalls

variable {n K : ℕ}

/-- A supported color lies inside its own primitive list, so the new physical
pin has singleton bounds; every old physical pin keeps its representation. -/
theorem supported_pinBounds (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (x : Fin n) (c : Fin (K + 1)) (hc : ∃ f, S.Valid f ∧ f x = c) :
    PinBounds (pinAt S x c) (recordPin pins x c) := by
  obtain ⟨f, hf, hfc⟩ := hc
  have hlo : S.lower x ≤ c := hfc ▸ (hf.1 x).1
  have hhi : c ≤ S.upper x := hfc ▸ (hf.1 x).2
  intro y d hyd
  by_cases hyx : y = x
  · subst y
    have hcd : c = d := by simpa using hyd
    subst d
    simp [pinAt, max_eq_right hlo, min_eq_right hhi]
  · have hold : pins y = some d := by simpa [recordPin, hyx] using hyd
    simpa [pinAt, hyx] using hp y d hold

/-- Pinning and then deleting all fixed-pin rows leaves an incomparable
reserved label's two effective endpoints exactly unchanged. -/
theorem eliminate_after_pin_windows (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (x y : Fin n) (c : Fin (K + 1)) (hc : ∃ f, S.Valid f ∧ f x = c)
    (hxy : closure S.edge x y = false) (hyx : closure S.edge y x = false) :
    (closeSystem (eliminatePins (pinAt S x c) (recordPin pins x c))).effectiveLower y =
        (closeSystem S).effectiveLower y ∧
    (closeSystem (eliminatePins (pinAt S x c) (recordPin pins x c))).effectiveUpper y =
        (closeSystem S).effectiveUpper y := by
  have hp' := supported_pinBounds S pins hp x c hc
  have hfeas : ∃ f, (pinAt S x c).Valid f := by
    obtain ⟨f, hf, hfx⟩ := hc
    exact ⟨f, (valid_pinAt S x c f).mpr ⟨hf, hfx⟩⟩
  have helim := PinElimination.windows_eq (pinAt S x c) (recordPin pins x c) hp' hfeas y
  have hpin := pin_windows_unchanged S x y c hxy hyx
  exact ⟨helim.1.trans hpin.1, helim.2.trans hpin.2⟩

/-- Distance greater than one preserves each free raw row incident to the
reserved label when the earlier pin's rows are removed. -/
theorem incident_row_survives (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (x y z : Fin n) (c : Fin (K + 1))
    (hfar : x ∉ ball S.edge y 1) (hy : pins y = none) (hz : pins z = none)
    (he : S.edge y z = true) :
    (eliminatePins (pinAt S x c) (recordPin pins x c)).edge y z = true := by
  have hyx : y ≠ x := by
    intro h
    subst x
    exact hfar (center_mem_ball _ _ _)
  have hzx : z ≠ x := by
    intro h
    subst x
    exact hfar ((mem_ball_one S.edge y z).mpr
      ((mem_closedNeighbors S.edge y z).mpr (Or.inr (Or.inl he))))
  have hpy : recordPin pins x c y = none := by simp [recordPin, hyx, hy]
  have hpz : recordPin pins x c z = none := by simp [recordPin, hzx, hz]
  rw [free_row _ _ hpy hpz]
  exact he

/-- The same statement for an incoming incident row. -/
theorem incoming_row_survives (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (x y z : Fin n) (c : Fin (K + 1))
    (hfar : x ∉ ball S.edge y 1) (hy : pins y = none) (hz : pins z = none)
    (he : S.edge z y = true) :
    (eliminatePins (pinAt S x c) (recordPin pins x c)).edge z y = true := by
  have hyx : y ≠ x := by
    intro h
    subst x
    exact hfar (center_mem_ball _ _ _)
  have hzx : z ≠ x := by
    intro h
    subst x
    exact hfar ((mem_ball_one S.edge y z).mpr
      ((mem_closedNeighbors S.edge y z).mpr (Or.inr (Or.inr he))))
  have hpy : recordPin pins x c y = none := by simp [recordPin, hyx, hy]
  have hpz : recordPin pins x c z = none := by simp [recordPin, hzx, hz]
  rw [free_row _ _ hpz hpy]
  exact he

/-- The `2H` separation proved for the concrete scale group implies both
window preservation and survival of every old free incident row. -/
theorem separated_pin_preserves (S : WeakSystem (Fin n) (K + 1))
    (pins : Fin n → Option (Fin (K + 1))) (hp : PinBounds S pins)
    (rank : Fin n → ℕ) (H : ℕ)
    (hstrict : ∀ u v, Arc S.edge u v → rank u < rank v)
    (hheight : ∀ v, rank v + 1 ≤ H)
    (x y : Fin n) (c : Fin (K + 1)) (hc : ∃ f, S.Valid f ∧ f x = c)
    (hfar : y ∉ ball S.edge x (2 * H)) (hy : pins y = none) :
    ((closeSystem (eliminatePins (pinAt S x c) (recordPin pins x c))).effectiveLower y =
        (closeSystem S).effectiveLower y ∧
      (closeSystem (eliminatePins (pinAt S x c) (recordPin pins x c))).effectiveUpper y =
        (closeSystem S).effectiveUpper y) ∧
    (∀ z, pins z = none →
      (S.edge y z = true → (eliminatePins (pinAt S x c) (recordPin pins x c)).edge y z = true) ∧
      (S.edge z y = true → (eliminatePins (pinAt S x c) (recordPin pins x c)).edge z y = true)) := by
  have hincomp := incomparable_of_separated S.edge rank H hstrict hheight x y hfar
  have hfar' : x ∉ ball S.edge y 1 := by
    intro h
    have hsym := ball_symm S.edge h
    have hH := hheight y
    exact hfar (ball_mono S.edge x (by omega : 1 ≤ 2 * H) hsym)
  exact ⟨eliminate_after_pin_windows S pins hp x y c hc hincomp.1 hincomp.2,
    fun z hz => ⟨incident_row_survives S pins x y z c hfar' hy hz,
      incoming_row_survives S pins x y z c hfar' hy hz⟩⟩

end SortingAdversary.Optimal.ScalePinPreservation
