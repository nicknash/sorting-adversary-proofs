import SortingAdversary.Continuous.LocalEnclosure

/-!
# Exact rational calculations and their real semantics

The executable routines use rational arithmetic.  Casting their inputs and
outputs to the reals commutes with every maximum, minimum, digit update, and
finite schedule.  Thus the interval certificates refer to the same updates
whose continuous invariant measure is proved in `Stationarity`.
-/

namespace SortingAdversary.Continuous.FiniteAveraging

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def System.toReal (D : System ι ℚ) : System ι ℝ where
  lower x := D.lower x
  upper x := D.upper x
  edge := D.edge

theorem digit_cast (S : ℕ) (j : Fin S) (y l u : ℚ) :
    ((digit S j y l u : ℚ) : ℝ) = digit S j (y : ℝ) (l : ℝ) (u : ℝ) := by
  simp [digit]

theorem conditionalLower_cast (D : System ι ℚ) (x : ι) (Y : ι → ℚ) :
    ((conditionalLower D x Y : ℚ) : ℝ) = conditionalLower D.toReal x (fun y => (Y y : ℝ)) := by
  exact (Finset.fold_hom (op := max) (m := fun q : ℚ => (q : ℝ))
    (fun a b => Rat.cast_max a b)).symm

theorem conditionalUpper_cast (D : System ι ℚ) (x : ι) (Y : ι → ℚ) :
    ((conditionalUpper D x Y : ℚ) : ℝ) = conditionalUpper D.toReal x (fun y => (Y y : ℝ)) := by
  exact (Finset.fold_hom (op := min) (m := fun q : ℚ => (q : ℝ))
    (fun a b => Rat.cast_min a b)).symm

theorem update_cast (D : System ι ℚ) (S : ℕ) (j : Fin S) (x : ι) (Y : ι → ℚ) :
    (fun y => ((update D S j x Y y : ℚ) : ℝ)) =
      update D.toReal S j x (fun y => (Y y : ℝ)) := by
  funext y
  by_cases hy : y = x
  · subst y
    simp only [update_self, digit_cast, conditionalLower_cast, conditionalUpper_cast]
  · simp [update_other, hy]

theorem fullSteps_cast (D : System ι ℚ) (S : ℕ) (steps : List (ι × Fin S)) (Y : ι → ℚ) :
    (fun y => ((fullSteps D S steps Y y : ℚ) : ℝ)) =
      fullSteps D.toReal S steps (fun y => (Y y : ℝ)) := by
  induction steps generalizing Y with
  | nil => rfl
  | cons step steps ih =>
      change (fun y => ((fullSteps D S steps (update D S step.2 step.1 Y) y : ℚ) : ℝ)) = _
      rw [ih, update_cast]
      rfl

theorem endpointEntry_cast (D : System ι ℚ) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) (x : ι) :
    (((endpointEntry D S schedule digits x).1 : ℝ),
      ((endpointEntry D S schedule digits x).2 : ℝ)) =
      endpointEntry D.toReal S schedule digits x := by
  apply Prod.ext
  · exact congrFun (fullSteps_cast D S (assignedSteps S schedule digits) D.lower) x
  · exact congrFun (fullSteps_cast D S (assignedSteps S schedule digits) D.upper) x

/-- Real trajectories are enclosed by the intervals actually computed over
the rationals, without any floating-point interpretation. -/
theorem rational_endpointEntry_encloses (D : System ι ℚ) (S : ℕ) (schedule : List ι)
    (digits : Fin schedule.length → Fin S) {Y : ι → ℝ}
    (hY : D.toReal.StrictlyFeasible Y) (x : ι) :
    ((endpointEntry D S schedule digits x).1 : ℝ) ≤
        fullSteps D.toReal S (assignedSteps S schedule digits) Y x ∧
      fullSteps D.toReal S (assignedSteps S schedule digits) Y x ≤
        ((endpointEntry D S schedule digits x).2 : ℝ) := by
  have hw : D.toReal.WeaklyFeasible Y :=
    ⟨fun y => ⟨(hY.1 y).1.le, (hY.1 y).2.le⟩, fun y z hyz => (hY.2 y z hyz).le⟩
  have h := endpointEntry_encloses D.toReal S schedule digits hw x
  have he := endpointEntry_cast D S schedule digits x
  rw [← he] at h
  exact h

end SortingAdversary.Continuous.FiniteAveraging
