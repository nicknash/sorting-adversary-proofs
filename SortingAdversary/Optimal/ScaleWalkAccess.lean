import SortingAdversary.Optimal.ScaleWalksWork

/-!
# Measured access to the actually reconstructed scale walk

Reconstruction builds one getter closure per chosen step. A vertex read
follows one predecessor closure at each index decrement, with an explicit
linear charge. The getter is proved equal to the deterministic `buildWalk`
vertex function, so no arbitrary walk function receives an assumed cost.
-/

namespace SortingAdversary.Optimal.ScaleWalkAccess

open PrimitiveWork GraphBalls ScaleGeometry ScaleWalksWork

variable {n : ℕ}

def build (E : Rows n) (x y : Fin n) : (r : ℕ) → y ∈ ball (relation E) x r →
    Result (Fin (r + 1) → Result (Fin n))
  | 0, _ => ⟨fun _ => ⟨x, 1⟩, 3⟩
  | r + 1, h =>
    let next := nextLabel E x y r h
    have reaches : y ∈ ball (relation E) next.value r := by
      rw [nextLabel_value]
      exact (ScaleWalks.nextLabel_spec (relation E) x y r h).2
    let tail := build E next.value y r reaches
    ⟨Fin.cases ⟨x, 1⟩ (fun i => let old := tail.value i; ⟨old.value, old.work + 2⟩),
      next.work + tail.work + 3⟩

private theorem vertex_congr (E : Rows n) (y : Fin n) (r : ℕ) {u v : Fin n}
    (heq : u = v) (hu : y ∈ ball (relation E) u r) (hv : y ∈ ball (relation E) v r)
    (i : Fin (r + 1)) :
    (ScaleWalks.buildWalk (relation E) u y r hu).val.vertex i =
      (ScaleWalks.buildWalk (relation E) v y r hv).val.vertex i := by
  subst v
  rfl

theorem build_value (E : Rows n) (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x r)
    (i : Fin (r + 1)) :
    ((build E x y r h).value i).value = (ScaleWalks.buildWalk (relation E) x y r h).val.vertex i := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [build, Fin.cases_succ, ScaleWalks.buildWalk, Walk.prepend, ih]
      exact vertex_congr E y r (nextLabel_value E x y r h) _ _ j

theorem get_work (E : Rows n) (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x r)
    (i : Fin (r + 1)) : ((build E x y r h).value i).work = 2 * i.val + 1 := by
  induction r generalizing x y with
  | zero =>
    have hi : i.val = 0 := by omega
    simp [build, hi]
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [build, Fin.cases_succ, Fin.val_succ, ih]
      omega

theorem get_work_le (E : Rows n) (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x r)
    (i : Fin (r + 1)) : ((build E x y r h).value i).work ≤ 2 * r + 1 := by
  rw [get_work]
  have hi := i.isLt
  omega

theorem build_work_eq (E : Rows n) (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x r) :
    (build E x y r h).work = (ScaleWalksWork.buildWalk E x y r h).work := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih => simp only [build, ScaleWalksWork.buildWalk, ih]

theorem build_work (E : Rows n) (C : ℕ) (cost : ∀ x y, (E x y).work ≤ C)
    (x y : Fin n) (r : ℕ) (h : y ∈ ball (relation E) x r) :
    (build E x y r h).work ≤ walkBound n r C := by
  rw [build_work_eq]
  exact buildWalk_work E C cost x y r h

end SortingAdversary.Optimal.ScaleWalkAccess
