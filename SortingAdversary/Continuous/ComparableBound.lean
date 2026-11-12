import SortingAdversary.Continuous.ComparableDensity
import SortingAdversary.Continuous.RationalSemantics
import SortingAdversary.Optimal.GraphBalls

/-!
# The comparable-coordinate bound from sparse graph invariants

Every ancestor or descendant lies in the undirected radius `H-1` ball when
the directed graph has a rank below `H`. A generating degree bound therefore
gives the manuscript's `B = (d+1)^(H+1)` bound on comparable coordinates.
The result applies directly to the real interpretation of rational systems.
-/

namespace SortingAdversary.Continuous.ComparableBound

open FiniteAveraging OrderRegion ComparableDensity
open SortingAdversary.Optimal.GraphBalls

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

theorem reaches_proper_arcs (D : System ι K) (rank : ι → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    {x y : ι} (hxy : Reaches D x y) : Relation.ReflTransGen (Arc D.edge) x y := by
  apply Relation.ReflTransGen.mono (r := fun u v => D.edge u v = true) (p := Arc D.edge) ?_ x y hxy
  intro u v huv
  refine ⟨?_, huv⟩
  rintro rfl
  exact Nat.lt_irrefl _ (hrank u u huv)

theorem comparable_mem_ball (D : System ι K) (rank : ι → ℕ) (H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (x y : ι)
    (hxy : Reaches D x y ∨ Reaches D y x) : y ∈ ball D.edge x (H - 1) := by
  rcases hxy with hxy | hyx
  · exact ball_symm D.edge (ancestor_mem_ball D.edge rank H
      (fun u v h => hrank u v h.2) hheight (reaches_proper_arcs D rank hrank hxy))
  · exact ancestor_mem_ball D.edge rank H
      (fun u v h => hrank u v h.2) hheight (reaches_proper_arcs D rank hrank hyx)

theorem comparableCount_le_ball_card (D : System ι ℝ) (rank : ι → ℕ) (H : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H) (x : ι) :
    comparableCount D x ≤ (ball D.edge x (H - 1)).card := by
  classical
  unfold comparableCount
  apply Finset.card_le_card_of_injOn (fun y : Remaining x => (y : ι))
  · intro y hy
    exact comparable_mem_ball D rank H hrank hheight x y (Finset.mem_filter.mp hy).2
  · exact Subtype.val_injective.injOn

theorem comparableCount_le_degree_height (D : System ι ℝ) (rank : ι → ℕ) (H d : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d) (x : ι) :
    comparableCount D x ≤ (d + 1) ^ (H + 1) := by
  exact (comparableCount_le_ball_card D rank H hrank hheight x).trans
    ((ball_card_le D.edge d hdegree x (H - 1)).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))

theorem comparableCount_toReal_le (D : System ι ℚ) (rank : ι → ℕ) (H d : ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ d) (x : ι) :
    comparableCount D.toReal x ≤ (d + 1) ^ (H + 1) :=
  comparableCount_le_degree_height D.toReal rank H d hrank hheight hdegree x

end SortingAdversary.Continuous.ComparableBound
