import SortingAdversary.Continuous.TreeState
import SortingAdversary.Continuous.Density

/-!
# Actual volume changes under tree refinement

The flat tree representation has one coordinate per item.  Restricting the
old parent coordinate and admitting the fresh unit coordinate therefore is
a measure-preserving reindexing of `section × (0,1)`.  This proves the volume
gain for the concrete state operation, including admission to an existing
child.  An isolated unit coordinate has density exactly one; this is the
fact that prevents a queried item from being refined twice before an answer.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion Density MeasureTheory Set

variable {n : ℕ}

theorem update_restore (x : Fin n) (c t : ℝ) (Y : Remaining x → ℝ) :
    Function.update (restore x t Y) x c = restore x c Y := by
  funext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [restore, hy]

theorem split_preimage_resetCoordinate (D : System (Fin n) ℝ)
    (x : Fin n) (c : ℝ) (hxx : D.edge x x = false)
    (hc : D.lower x < c ∧ c < D.upper x) :
    (splitEquiv x) ⁻¹' region (resetCoordinate D x c) =
      sectionAt D x c ×ˢ Ioo (0 : ℝ) 1 := by
  ext p
  rw [mem_preimage, splitEquiv_apply]
  change (resetCoordinate D x c).StrictlyFeasible (restore x p.2 p.1) ↔ _
  rw [resetCoordinate_feasible_iff D x c hxx hc, restore_self, update_restore]
  simp only [mem_prod, sectionAt, mem_ofPred_eq, mem_Ioo]
  exact and_comm

/-- The reset state's actual Lebesgue volume is the actual coordinate-section
volume.  The factor contributed by the new child coordinate is exactly one. -/
theorem resetCoordinate_volume (D : System (Fin n) ℝ) (x : Fin n) (c : ℝ)
    (hxx : D.edge x x = false) (hc : D.lower x < c ∧ c < D.upper x) :
    volume (region (resetCoordinate D x c)) = volume (sectionAt D x c) := by
  have hm := (splitEquiv_measurePreserving x).measure_preimage
    (region_open (resetCoordinate D x c)).measurableSet.nullMeasurableSet
  rw [split_preimage_resetCoordinate D x c hxx hc, Measure.volume_eq_prod,
    Measure.prod_prod] at hm
  simpa using hm.symm

/-- The exact multiplicative gain for the actual tree mutation. -/
theorem refineAt_volume_identity (s : State n ℝ) (x : Fin n) (c : ℝ)
    (hxx : s.system.edge x x = false)
    (hc : s.system.lower x < c ∧ c < s.system.upper x)
    (hV : 0 < nodeVolume s.system) :
    nodeVolume (refineAt s x c).system = nodeVolume s.system * density s.system x c := by
  change (volume (region (resetCoordinate s.system x c))).toReal = _
  rw [resetCoordinate_volume s.system x c hxx hc]
  change sectionVolume s.system x c = _
  rw [density, mul_div_cancel₀ _ (ne_of_gt hV)]

theorem refineAt_volume_pos (s : State n ℝ) (x : Fin n) (c : ℝ)
    (hD : Normalized s.system) (hw : ∀ y, s.system.lower y < s.system.upper y)
    {m : ℕ} (rank : Fin n → Fin m)
    (horder : ∀ y z, s.system.edge y z = true → rank y < rank z)
    (hc : s.system.lower x < c ∧ c < s.system.upper x) :
    0 < nodeVolume (refineAt s x c).system := by
  have hxx : s.system.edge x x = false := by
    cases he : s.system.edge x x with
    | false => rfl
    | true => exact (lt_irrefl _ (horder x x he)).elim
  apply nodeVolume_pos
  change 0 < volume (region (resetCoordinate s.system x c))
  rw [resetCoordinate_volume s.system x c hxx hc,
    section_eq_restrictAt s.system x c hxx hc]
  exact restriction_volume_pos s.system hD hw rank horder x c hc

def IsolatedUnit (D : System (Fin n) ℝ) (x : Fin n) : Prop :=
  D.lower x = 0 ∧ D.upper x = 1 ∧
    ∀ y, D.edge x y = false ∧ D.edge y x = false

theorem refineAt_isolatedUnit (s : State n ℝ) (x : Fin n) (c : ℝ) :
    IsolatedUnit (refineAt s x c).system x := by
  exact ⟨(refineAt_unit s x c).1, (refineAt_unit s x c).2,
    fun y => refineAt_isolated s x y c⟩

theorem resetCoordinate_eq_of_isolatedUnit (D : System (Fin n) ℝ) (x : Fin n)
    (c : ℝ) (h : IsolatedUnit D x) : resetCoordinate D x c = D := by
  rcases D with ⟨lower, upper, edge⟩
  rcases h with ⟨hl, hu, he⟩
  dsimp only at hl hu he
  unfold resetCoordinate
  congr 1
  · funext y
    by_cases hy : y = x
    · subst y
      simpa using hl.symm
    · simp [hy, (he y).1]
  · funext y
    by_cases hy : y = x
    · subst y
      simpa using hu.symm
    · simp [hy, (he y).2]
  · funext y z
    by_cases hy : y = x
    · subst y
      simp [(he z).1]
    · by_cases hz : z = x
      · subst z
        simp [(he y).2]
      · simp [hy, hz]

theorem isolatedUnit_density (D : System (Fin n) ℝ) (x : Fin n)
    (h : IsolatedUnit D x) (hV : 0 < nodeVolume D) (c : ℝ) (hc : 0 < c ∧ c < 1) :
    density D x c = 1 := by
  have hcx : D.lower x < c ∧ c < D.upper x := by simpa [h.1, h.2.1] using hc
  have heq := resetCoordinate_volume D x c (h.2.2 x).1 hcx
  rw [resetCoordinate_eq_of_isolatedUnit D x c h] at heq
  have hs : sectionVolume D x c = nodeVolume D := congrArg ENNReal.toReal heq.symm
  rw [density, hs, div_self (ne_of_gt hV)]

/-- Refining another item does not change a fresh isolated coordinate. -/
theorem resetCoordinate_preserves_isolatedUnit (D : System (Fin n) ℝ)
    (x y : Fin n) (c : ℝ) (h : IsolatedUnit D x) :
    IsolatedUnit (resetCoordinate D y c) x := by
  by_cases hxy : x = y
  · subst x
    exact refineAt_isolatedUnit ⟨D, fun _ => []⟩ y c
  · refine ⟨?_, ?_, ?_⟩
    · simp [resetCoordinate, hxy, (h.2.2 y).2, h.1]
    · simp [resetCoordinate, hxy, (h.2.2 y).1, h.2.1]
    · intro z
      simp [resetCoordinate, hxy, (h.2.2 z).1, (h.2.2 z).2]

end SortingAdversary.Continuous.TreeState
