import SortingAdversary.Continuous.GraphOrder
import SortingAdversary.Continuous.OneArcRepair

/-!
# Positive volume supplies the graph ranks used by the local proofs

A feasible assignment induces a strict finite rank by counting coordinates
below each value. Thus a positive-volume state is acyclic without carrying a
rank oracle. The executable longest-path table then supplies a short rank
whenever the graph has the required directed-path bound.
-/

namespace SortingAdversary.Continuous.OrderRegion

open FiniteAveraging MeasureTheory
open SortingAdversary.Optimal.GraphBalls
open SortingAdversary.Optimal.SparseRepairGraph

variable {n : ℕ}

theorem rank_of_feasible (D : System (Fin n) ℝ) {X : Fin n → ℝ}
    (hX : D.StrictlyFeasible X) :
    ∃ rank : Fin n → ℕ, (∀ x, rank x < n) ∧
      ∀ x y, D.edge x y = true → rank x < rank y := by
  classical
  let lower (x : Fin n) := Finset.univ.filter (fun y => X y < X x)
  refine ⟨fun x => (lower x).card, ?_, ?_⟩
  · intro x
    have hs : lower x ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      intro he
      have hx : x ∈ lower x := by rw [he]; exact Finset.mem_univ x
      simp [lower] at hx
    simpa using Finset.card_lt_card hs
  · intro x y hxy
    have hlt := hX.2 x y hxy
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.trans hlt⟩
    · intro he
      have hx : x ∈ lower y := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlt⟩
      rw [← he] at hx
      simp [lower] at hx

theorem rank_of_positive (D : System (Fin n) ℝ) (hV : 0 < volume (region D)) :
    ∃ rank : Fin n → ℕ, (∀ x, rank x < n) ∧
      ∀ x y, D.edge x y = true → rank x < rank y := by
  obtain ⟨X, hX⟩ := (volume_pos_iff_nonempty D).mp hV
  exact rank_of_feasible D hX

theorem no_loop_of_positive (D : System (Fin n) ℝ) (hV : 0 < volume (region D)) :
    ∀ x, D.edge x x = false := by
  obtain ⟨X, hX⟩ := (volume_pos_iff_nonempty D).mp hV
  intro x
  apply Bool.eq_false_iff.mpr
  intro hx
  exact (lt_irrefl _ (hX.2 x x hx))

theorem widths_of_positive (D : System (Fin n) ℝ) (hV : 0 < volume (region D)) :
    ∀ x, D.lower x < D.upper x := by
  obtain ⟨X, hX⟩ := (volume_pos_iff_nonempty D).mp hV
  exact fun x => (hX.1 x).1.trans (hX.1 x).2

/-- A strict path bound gives a strict rank below the same threshold. The
rank is the executable dynamic-programming longest-path rank. -/
theorem short_rank_of_height (D : System (Fin n) ℝ) (hV : 0 < volume (region D))
    (H : ℕ) (hH : OneArcRepair.HeightBelow D.edge H) :
    ∃ rank : Fin n → ℕ,
      (∀ x y, D.edge x y = true → rank x < rank y) ∧
      ∀ x, rank x + 1 < H := by
  obtain ⟨r, hrbound, hr⟩ := rank_of_positive D hV
  have hlo := no_loop_of_positive D hV
  have hrs : ∀ x y, Arc D.edge x y → r x < r y := fun x y h => hr x y h.2
  have hh := (OneArcRepair.computed_height_iff D.edge r n H hrs hrbound).mpr hH
  refine ⟨heightRank D.edge r n, ?_, ?_⟩
  · intro x y hxy
    apply heightRank_strict D.edge r n hrs hrbound
    refine ⟨?_, hxy⟩
    intro he
    subst y
    simp [hlo x] at hxy
  · intro x
    exact (heightRank_bound D.edge r n hrs hrbound x).trans_lt hh

end SortingAdversary.Continuous.OrderRegion
