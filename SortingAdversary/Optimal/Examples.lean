import SortingAdversary.Optimal.Endpoints
import SortingAdversary.Optimal.LocalChoice
import SortingAdversary.Optimal.Refinement
import SortingAdversary.Optimal.Parameters
import SortingAdversary.Basic

/-!
# Small checks of the intended semantics

These use ordinary kernel reduction (`decide`), never a native evaluator axiom.
They check the distinctions that matter for the new construction: overlapping
weak branches, unchanged old lists, physical colour identities, and the fact
that a nonempty set of weak maps alone does not certify a legal strict order.
-/

namespace SortingAdversary.Optimal.Examples

open WeakMaps WeakMaps.WeakSystem

def twoLabels : WeakSystem (Fin 2) 2 := Endpoints.initialSystem (Fin 2) 1

theorem twoLabels_count : twoLabels.count = 4 := by decide

theorem twoLabels_weak_branches_overlap :
    (twoLabels.addRow 0 1).count = 3 ∧
      (twoLabels.addRow 1 0).count = 3 ∧
      (twoLabels.maps.filter (fun f => f 0 = f 1)).card = 2 := by
  decide

theorem extra_top_colour_does_not_expand_old_lists : twoLabels.enlarge.count = 4 := by
  rw [count_enlarge, twoLabels_count]

theorem fresh_birth_uses_the_new_palette : twoLabels.enlarge.birth.count = 12 := by
  rw [count_birth, count_enlarge, twoLabels_count]

/-- All three weak cycle inequalities can hold on a constant colour map. -/
def weakCycle : WeakSystem (Fin 3) 3 where
  edge := fun u v => decide ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 0))
  lower := fun _ => 0
  upper := fun _ => 2

theorem weakCycle_nonempty : weakCycle.count = 3 := by decide

/-- The same three *strict physical answers* cannot occur in any ranking.
This guards against using `choose_has_map` as a public-legality certificate. -/
theorem strict_cycle_has_no_ranking :
    ¬ ∃ π : Ranking 3, π 0 < π 1 ∧ π 1 < π 2 ∧ π 2 < π 0 := by
  rintro ⟨π, h01, h12, h20⟩
  exact (lt_irrefl (π 0)) (lt_trans (lt_trans h01 h12) h20)

def lowerExample (x : Fin 3) : ℕ := if x = 2 then 1 else 0

theorem lower_endpoint_split_changes_identities_correctly :
    Refinement.liftMap (fun x y : Fin 3 => x ≤ y) 0 0 lowerExample 0 = 1 ∧
    Refinement.liftMap (fun x y : Fin 3 => x ≤ y) 0 0 lowerExample 1 = 1 ∧
    Refinement.liftMap (fun x y : Fin 3 => x ≤ y) 0 0 lowerExample 2 = 2 := by
  decide

def upperExample (x : Fin 3) : ℕ := if x = 0 then 0 else 1

theorem upper_endpoint_split_changes_identities_correctly :
    Refinement.liftMapBefore (fun x y : Fin 3 => x ≤ y) 2 1 upperExample 0 = 0 ∧
    Refinement.liftMapBefore (fun x y : Fin 3 => x ≤ y) 2 1 upperExample 1 = 1 ∧
    Refinement.embedBefore 1 1 = 2 := by
  decide

theorem bounded_stage_scan_stops_at_first_rejection :
    Parameters.scanAffordable (fun j => j * j) 9 0 20 = ⟨3, 4⟩ := by decide

end SortingAdversary.Optimal.Examples
