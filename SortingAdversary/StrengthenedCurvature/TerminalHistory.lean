import SortingAdversary.Strategy
import SortingAdversary.StrengthenedCurvature.InformativeHistory
import Mathlib.Tactic.Order

/-!
# Terminal transcripts contain the adjacent comparisons

A correct sorting leaf has only one compatible ranking.  Swapping two
adjacent ranks shows that the transcript must therefore contain their direct
comparison.  This is the combinatorial input to the terminal path-determinant
estimate.
-/

namespace SortingAdversary
namespace StrengthenedCurvature

/-- Swap the ranks of two labelled items. -/
def swapRanks (π : Ranking n) (u v : Item n) : Ranking n :=
  π.trans (Equiv.swap (π u) (π v))

@[simp] theorem swapRanks_apply_left (π : Ranking n) (u v : Item n) :
    swapRanks π u v u = π v := by
  simp [swapRanks, Equiv.trans_apply]

@[simp] theorem swapRanks_apply_right (π : Ranking n) (u v : Item n) :
    swapRanks π u v v = π u := by
  simp [swapRanks, Equiv.trans_apply]

@[simp] theorem swapRanks_apply_of_ne (π : Ranking n) {u v x : Item n}
    (hxu : x ≠ u) (hxv : x ≠ v) : swapRanks π u v x = π x := by
  have h₁ : π x ≠ π u := fun h => hxu (π.injective h)
  have h₂ : π x ≠ π v := fun h => hxv (π.injective h)
  simp [swapRanks, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂]

/-- Swapping adjacent ranks preserves every strict comparison except the
comparison from the lower swapped item to the upper one. -/
theorem swapRanks_lt_of_lt_of_not_pair (π : Ranking n) {u v x y : Item n}
    (hadj : (π u).val + 1 = (π v).val) (hxy : π x < π y)
    (hpair : ¬(x = u ∧ y = v)) :
    swapRanks π u v x < swapRanks π u v y := by
  by_cases hxu : x = u
  · subst x
    by_cases hyv : y = v
    · exact (hpair ⟨rfl, hyv⟩).elim
    · have hyu : y ≠ u := by
        intro hyu
        subst y
        simp at hxy
      have hne : (π y).val ≠ (π v).val := by
        intro heq
        exact hyv (π.injective (Fin.ext heq))
      rw [swapRanks_apply_left, swapRanks_apply_of_ne π hyu hyv]
      change (π u).val < (π y).val at hxy
      change (π v).val < (π y).val
      omega
  · by_cases hxv : x = v
    · subst x
      have hyu : y ≠ u := by
        intro hyu
        subst y
        change (π v).val < (π u).val at hxy
        omega
      have hyv : y ≠ v := by
        intro hyv
        subst y
        simp at hxy
      rw [swapRanks_apply_right, swapRanks_apply_of_ne π hyu hyv]
      change (π v).val < (π y).val at hxy
      change (π u).val < (π y).val
      omega
    · by_cases hyu : y = u
      · subst y
        rw [swapRanks_apply_of_ne π hxu hxv, swapRanks_apply_left]
        change (π x).val < (π u).val at hxy
        change (π x).val < (π v).val
        omega
      · by_cases hyv : y = v
        · subst y
          have hne : (π x).val ≠ (π u).val := by
            intro heq
            exact hxu (π.injective (Fin.ext heq))
          rw [swapRanks_apply_of_ne π hxu hxv, swapRanks_apply_right]
          change (π x).val < (π v).val at hxy
          change (π x).val < (π u).val
          omega
        · rw [swapRanks_apply_of_ne π hxu hxv,
            swapRanks_apply_of_ne π hyu hyv]
          exact hxy

/-- If a ranking is compatible with a history, swapping adjacent items remains
compatible unless their oriented direct comparison occurs in the history. -/
theorem compatible_swapRanks_of_adjacent_not_observed
    (π : Ranking n) (h : History n) {u v : Item n}
    (hπ : Compatible π h) (hadj : (π u).val + 1 = (π v).val)
    (hmissing : ∀ o ∈ h, ¬(lower o = u ∧ upper o = v)) :
    Compatible (swapRanks π u v) h := by
  rw [Compatible, List.forall_iff_forall_mem] at hπ ⊢
  intro o ho
  rw [holds_iff_lower_lt_upper]
  apply swapRanks_lt_of_lt_of_not_pair π hadj
  · exact (holds_iff_lower_lt_upper π o).1 (hπ o ho)
  · exact hmissing o ho

/-- A correct tree's completed run has a unique compatible ranking. -/
theorem compatible_unique_of_correct_run (t : DecisionTree n) (strategy : Strategy n)
    (ht : t.Correct) {π τ : Ranking n}
    (hπ : Compatible π (t.run strategy []).observations)
    (hτ : Compatible τ (t.run strategy []).observations) : π = τ := by
  have hπrun := t.run_matches_compatible_ranking strategy [] π hπ
  have hτrun := t.run_matches_compatible_ranking strategy [] τ hτ
  calc
    π = t.evaluate π := (ht π).symm
    _ = (t.run strategy []).output := hπrun.1
    _ = t.evaluate τ := hτrun.1.symm
    _ = τ := ht τ

/-- In any history with a unique compatible ranking, every adjacent relation
of that ranking occurs as an oriented direct observation. -/
theorem exists_adjacent_observation_of_unique_compatible
    (h : History n) (π : Ranking n) (hπ : Compatible π h)
    (hunique : ∀ τ : Ranking n, Compatible τ h → τ = π)
    {u v : Item n} (hadj : (π u).val + 1 = (π v).val) :
    ∃ o ∈ h, lower o = u ∧ upper o = v := by
  by_contra hnone
  have hmissing : ∀ o ∈ h, ¬(lower o = u ∧ upper o = v) := by
    simpa only [not_exists, not_and] using hnone
  have hswap := compatible_swapRanks_of_adjacent_not_observed π h hπ hadj hmissing
  have heq : swapRanks π u v = π := hunique _ hswap
  have hu : swapRanks π u v u = π u := congrArg (fun ρ : Ranking n => ρ u) heq
  rw [swapRanks_apply_left] at hu
  have huv : v = u := π.injective hu
  subst v
  simp at hadj

/-- Every pair of adjacent items in a compatible terminal ranking occurs as
an oriented direct comparison in the completed transcript. -/
theorem exists_adjacent_observation_of_correct_run
    (t : DecisionTree n) (strategy : Strategy n) (ht : t.Correct)
    (π : Ranking n) (hπ : Compatible π (t.run strategy []).observations)
    {u v : Item n} (hadj : (π u).val + 1 = (π v).val) :
    ∃ o ∈ (t.run strategy []).observations,
      lower o = u ∧ upper o = v := by
  apply exists_adjacent_observation_of_unique_compatible _ π hπ _ hadj
  intro τ hτ
  exact (compatible_unique_of_correct_run t strategy ht hτ hπ)

end StrengthenedCurvature
end SortingAdversary
