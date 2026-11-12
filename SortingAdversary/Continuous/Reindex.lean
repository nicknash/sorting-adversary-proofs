import SortingAdversary.Continuous.Normalization
import Mathlib.Data.List.NodupEquivFin

/-!
# Executable topological relabeling

The finite sweep proof uses increasing `Fin` indices. Sorting an explicit
strict rank gives a computable permutation from these indices to the original
labels. Reindexing preserves the constraint semantics and commutes with the
actual conditional endpoints, digit updates, and finite trajectories.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

def System.reindex {ι κ K : Type*} (D : System ι K) (e : κ ≃ ι) : System κ K where
  lower x := D.lower (e x)
  upper x := D.upper (e x)
  edge x y := D.edge (e x) (e y)

section Algebra

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem System.reindex_strictlyFeasible_iff (D : System ι K) (e : κ ≃ ι) (Y : κ → K) :
    (D.reindex e).StrictlyFeasible Y ↔ D.StrictlyFeasible (fun x => Y (e.symm x)) := by
  constructor
  · intro h
    constructor
    · intro x
      simpa [System.reindex] using h.1 (e.symm x)
    · intro x y hxy
      exact h.2 (e.symm x) (e.symm y) (by simpa [System.reindex] using hxy)
  · intro h
    constructor
    · intro x
      simpa [System.reindex] using h.1 (e x)
    · intro x y hxy
      simpa using h.2 (e x) (e y) hxy

theorem System.reindex_feasible (D : System ι K) (e : κ ≃ ι) (X : ι → K) :
    (D.reindex e).StrictlyFeasible (fun x => X (e x)) ↔ D.StrictlyFeasible X := by
  rw [System.reindex_strictlyFeasible_iff]
  simp only [Equiv.apply_symm_apply]

theorem conditionalLower_reindex (D : System ι K) (e : κ ≃ ι) (v : κ) (X : ι → K) :
    conditionalLower (D.reindex e) v (fun x => X (e x)) = conditionalLower D (e v) X := by
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨lower_le_conditionalLower D (e v) X, ?_⟩
    intro w hw
    exact predecessor_le_conditionalLower D (e v) (e w) X (Finset.mem_filter.mp hw).2
  · apply (Finset.fold_max_le _).mpr
    refine ⟨lower_le_conditionalLower (D.reindex e) v _, ?_⟩
    intro w hw
    have he : (D.reindex e).edge (e.symm w) v = true := by
      simpa [System.reindex] using hw
    simpa using predecessor_le_conditionalLower (D.reindex e) v (e.symm w)
      (fun x => X (e x)) he

theorem conditionalUpper_reindex (D : System ι K) (e : κ ≃ ι) (v : κ) (X : ι → K) :
    conditionalUpper (D.reindex e) v (fun x => X (e x)) = conditionalUpper D (e v) X := by
  apply le_antisymm
  · apply (Finset.le_fold_min _).mpr
    refine ⟨conditionalUpper_le_upper (D.reindex e) v _, ?_⟩
    intro w hw
    have he : (D.reindex e).edge v (e.symm w) = true := by
      simpa [System.reindex] using hw
    simpa using conditionalUpper_le_successor (D.reindex e) v (e.symm w)
      (fun x => X (e x)) he
  · apply (Finset.le_fold_min _).mpr
    refine ⟨conditionalUpper_le_upper D (e v) X, ?_⟩
    intro w hw
    exact conditionalUpper_le_successor D (e v) (e w) X (Finset.mem_filter.mp hw).2

theorem update_reindex (D : System ι K) (e : κ ≃ ι) (S : ℕ) (j : Fin S)
    (v : κ) (X : ι → K) :
    update (D.reindex e) S j v (fun x => X (e x)) =
      (fun x => update D S j (e v) X (e x)) := by
  funext x
  by_cases hx : x = v
  · subst x
    simp only [update_self, conditionalLower_reindex, conditionalUpper_reindex]
  · rw [update_other _ _ _ _ _ _ hx,
      update_other _ _ _ _ _ _ (fun he => hx (e.injective he))]

theorem fullSteps_reindex (D : System ι K) (e : κ ≃ ι) (S : ℕ)
    (steps : List (κ × Fin S)) (X : ι → K) :
    fullSteps (D.reindex e) S steps (fun x => X (e x)) =
      (fun x => fullSteps D S (steps.map fun step => (e step.1, step.2)) X (e x)) := by
  induction steps generalizing X with
  | nil => rfl
  | cons step steps ih =>
    change fullSteps (D.reindex e) S steps
      (update (D.reindex e) S step.2 step.1 (fun x => X (e x))) = _
    rw [update_reindex, ih]
    rfl

end Algebra

theorem System.reindex_toReal {ι κ : Type*} (D : System ι ℚ) (e : κ ≃ ι) :
    (D.reindex e).toReal = D.toReal.reindex e := rfl

end SortingAdversary.Continuous.FiniteAveraging

namespace SortingAdversary.Continuous.OrderRegion

open FiniteAveraging

theorem normalized_reindex {ι κ K : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (D : System ι K) (e : κ ≃ ι) (hD : Normalized D) : Normalized (D.reindex e) := by
  intro x y hxy
  exact hD (e x) (e y) hxy

/-- The computable permutation sending increasing sweep indices to their
original labels in the rank-sorted list. -/
def rankEquiv {n : ℕ} (rank : Fin n → ℕ) : Fin n ≃ Fin n :=
  (finCongr (rankOrder_length rank).symm).trans
    (List.Nodup.getEquivOfForallMemList (rankOrder rank) (rankOrder_nodup rank)
      (mem_rankOrder rank))

theorem rankEquiv_apply {n : ℕ} (rank : Fin n → ℕ) (i : Fin n) :
    rankEquiv rank i = (rankOrder rank).get ⟨i.val, by rw [rankOrder_length]; exact i.isLt⟩ := rfl

theorem rankEquiv_rank_mono {n : ℕ} (rank : Fin n → ℕ) :
    Monotone (fun i => rank (rankEquiv rank i)) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · have h := (rankOrder_sorted rank).rel_get_of_lt
      (show (⟨i.val, by rw [rankOrder_length]; exact i.isLt⟩ : Fin (rankOrder rank).length) <
        ⟨j.val, by rw [rankOrder_length]; exact j.isLt⟩ from hij)
    simpa only [rankEquiv_apply] using h

theorem reindex_rankEquiv_order {K : Type*} {n : ℕ} (D : System (Fin n) K)
    (rank : Fin n → ℕ) (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ i j, (D.reindex (rankEquiv rank)).edge i j = true → i.val < j.val := by
  intro i j hij
  by_contra h
  have hji : j ≤ i := by omega
  exact (Nat.not_lt_of_ge (rankEquiv_rank_mono rank hji))
    (hrank (rankEquiv rank i) (rankEquiv rank j) hij)

/-- A concrete normalization and relabeling step produces precisely the
index convention required by the finite averaging width calculation. -/
def canonicalReindex {K : Type*} [LinearOrder K] {n : ℕ}
    (D : System (Fin n) K) (rank : Fin n → ℕ) : System (Fin n) K :=
  (normalize D (rankOrder rank)).reindex (rankEquiv rank)

theorem canonicalReindex_normalized {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    Normalized (canonicalReindex D rank) :=
  normalized_reindex _ _ (normalize_rankOrder_normalized D rank hrank)

theorem canonicalReindex_order {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ i j, (canonicalReindex D rank).edge i j = true → i.val < j.val := by
  apply reindex_rankEquiv_order (normalize D (rankOrder rank)) rank
  simpa only [normalize_edge] using hrank

theorem canonicalReindex_feasible {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (D : System (Fin n) K) (rank : Fin n → ℕ)
    (X : Fin n → K) :
    (canonicalReindex D rank).StrictlyFeasible (fun i => X (rankEquiv rank i)) ↔
      D.StrictlyFeasible X := by
  rw [canonicalReindex, System.reindex_feasible, normalize_feasible_iff]

end SortingAdversary.Continuous.OrderRegion
