import SortingAdversary.Continuous.RationalSemantics
import SortingAdversary.Continuous.TreeRouting

/-!
# Real semantics of the rational tree program

All stored endpoints and child positions are exact rationals. Casting them
to reals commutes with each concrete tree mutation and with normalization.
This lets the executable controller use the geometric state theorems without
replacing its arithmetic or its branch decisions by real-valued oracles.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion

variable {n : ℕ}

def State.toReal (s : State n ℚ) : State n ℝ where
  system := s.system.toReal
  location x := (s.location x).map (fun c => (c : ℝ))

@[simp] theorem initial_toReal (n : ℕ) :
    (initial n : State n ℚ).toReal = initial n := by
  simp [State.toReal, initial, System.toReal]

@[simp] theorem resetCoordinate_toReal (D : System (Fin n) ℚ) (x : Fin n) (c : ℚ) :
    (resetCoordinate D x c).toReal = resetCoordinate D.toReal x (c : ℝ) := by
  cases D with
  | mk lower upper edge =>
    unfold resetCoordinate System.toReal
    congr 1
    · funext y
      by_cases hy : y = x <;> by_cases he : edge x y = true <;> simp [hy, he]
    · funext y
      by_cases hy : y = x <;> by_cases he : edge y x = true <;> simp [hy, he]

@[simp] theorem refineAt_toReal (s : State n ℚ) (x : Fin n) (c : ℚ) :
    (refineAt s x c).toReal = refineAt s.toReal x (c : ℝ) := by
  unfold refineAt State.toReal
  congr 1
  · exact resetCoordinate_toReal s.system x c
  · funext y
    by_cases hy : y = x <;> simp [hy]

def Routing.toReal : Routing ℚ → Routing ℝ
  | .coordinates => .coordinates
  | .leftFree c => .leftFree c
  | .rightFree c => .rightFree c
  | .anchors c d => .anchors c d

@[simp] theorem route_toReal (p q : List ℚ) :
    route (p.map (fun c => (c : ℝ))) (q.map (fun c => (c : ℝ))) =
      (route p q).toReal := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons c cs ih =>
    cases q with
    | nil => rfl
    | cons d ds =>
      by_cases hcd : c = d
      · subst d
        simpa [route] using ih ds
      · have hcast : (c : ℝ) ≠ (d : ℝ) := by exact_mod_cast hcd
        simp [route, hcd, hcast, Routing.toReal]

@[simp] theorem addArc_toReal (D : System (Fin n) ℚ) (x y : Fin n) :
    (addArc D x y).toReal = addArc D.toReal x y := rfl

@[simp] theorem boundBelow_toReal (D : System (Fin n) ℚ) (x : Fin n) (c : ℚ) :
    (boundBelow D x c).toReal = boundBelow D.toReal x (c : ℝ) := by
  unfold boundBelow System.toReal
  congr 1
  funext y
  by_cases hy : y = x <;> simp [hy]

@[simp] theorem boundAbove_toReal (D : System (Fin n) ℚ) (x : Fin n) (c : ℚ) :
    (boundAbove D x c).toReal = boundAbove D.toReal x (c : ℝ) := by
  unfold boundAbove System.toReal
  congr 1
  funext y
  by_cases hy : y = x <;> simp [hy]

@[simp] theorem recordSystem_toReal (D : System (Fin n) ℚ) (r : Routing ℚ)
    (x y : Fin n) (a : Answer) :
    (recordSystem D r x y a).toReal = recordSystem D.toReal r.toReal x y a := by
  cases r <;> cases a <;> simp [recordSystem, Routing.toReal]

@[simp] theorem record_toReal (s : State n ℚ) (q : Query n) (a : Answer) :
    (record s q a).toReal = record s.toReal q a := by
  unfold record State.toReal
  simp only [route_toReal, recordSystem_toReal]

@[simp] theorem propagateLower_toReal (D : System (Fin n) ℚ) (x : Fin n) :
    (propagateLower D x).toReal = propagateLower D.toReal x := by
  unfold propagateLower System.toReal
  congr 1
  funext y
  by_cases hy : y = x
  · subst y
    simp only [Function.update_self]
    exact conditionalLower_cast D x D.lower
  · simp [hy]

@[simp] theorem propagateUpper_toReal (D : System (Fin n) ℚ) (x : Fin n) :
    (propagateUpper D x).toReal = propagateUpper D.toReal x := by
  unfold propagateUpper System.toReal
  congr 1
  funext y
  by_cases hy : y = x
  · subst y
    simp only [Function.update_self]
    exact conditionalUpper_cast D x D.upper
  · simp [hy]

theorem normalizeSystem_toReal (D : System (Fin n) ℚ) (order : List (Fin n)) :
    (OrderRegion.normalize D order).toReal = OrderRegion.normalize D.toReal order := by
  have hl : ∀ (xs : List (Fin n)) (D : System (Fin n) ℚ),
      (xs.foldl propagateLower D).toReal = xs.foldl propagateLower D.toReal := by
    intro xs
    induction xs with
    | nil => intro D; rfl
    | cons x xs ih => intro D; simp only [List.foldl_cons, ih, propagateLower_toReal]
  have hu : ∀ (xs : List (Fin n)) (D : System (Fin n) ℚ),
      (xs.foldl propagateUpper D).toReal = xs.foldl propagateUpper D.toReal := by
    intro xs
    induction xs with
    | nil => intro D; rfl
    | cons x xs ih => intro D; simp only [List.foldl_cons, ih, propagateUpper_toReal]
  simp only [OrderRegion.normalize, hu, hl]

@[simp] theorem normalize_toReal (s : State n ℚ) (order : List (Fin n)) :
    (normalize s order).toReal = normalize s.toReal order := by
  unfold normalize State.toReal
  simp only [normalizeSystem_toReal]

end SortingAdversary.Continuous.TreeState
