import SortingAdversary.Continuous.TreeState
import SortingAdversary.Continuous.RegionMeasure

/-!
# Routing comparisons and recording their constraints

Removing the common prefix of two stored paths reaches exactly the node used
by `Compare`.  The resulting pair consists of two free coordinates, one free
coordinate and one child anchor, or two distinct child anchors.  This file
implements that routing and the corresponding arc or endpoint update.

The recorded region is the old region intersected with the literal strict
comparison tested by `Select`.  For different child blocks, routing itself
determines the answer and the region is unchanged.
-/

namespace SortingAdversary.Continuous.TreeState

open FiniteAveraging OrderRegion

inductive Routing (K : Type*) where
  | coordinates
  | leftFree (c : K)
  | rightFree (c : K)
  | anchors (c d : K)
  deriving DecidableEq, Repr

section OrderedField

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def route : List K → List K → Routing K
  | [], [] => .coordinates
  | [], c :: _ => .leftFree c
  | c :: _, [] => .rightFree c
  | c :: cs, d :: ds => if c = d then route cs ds else .anchors c d

def Routing.Less (r : Routing K) (a b : K) : Prop :=
  match r with
  | .coordinates => a < b
  | .leftFree c => a < c
  | .rightFree c => c < b
  | .anchors c d => c < d

def Routing.Greater (r : Routing K) (a b : K) : Prop :=
  match r with
  | .coordinates => b < a
  | .leftFree c => c < a
  | .rightFree c => b < c
  | .anchors c d => d < c

def Routing.Holds (r : Routing K) (a b : K) (answer : Answer) : Prop :=
  match answer with
  | .less => r.Less a b
  | .greater => r.Greater a b

theorem route_less_sound (p q : List K) (a b : K)
    (h : (route p q).Less a b) : p ++ [a] < q ++ [b] := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => exact List.Lex.rel h
      | cons c cs => exact List.Lex.rel h
  | cons c cs ih =>
      cases q with
      | nil => exact List.Lex.rel h
      | cons d ds =>
          by_cases hcd : c = d
          · subst d
            exact List.Lex.cons (ih ds (by simpa [route] using h))
          · exact List.Lex.rel (by simpa [route, hcd, Routing.Less] using h)

theorem route_greater_sound (p q : List K) (a b : K)
    (h : (route p q).Greater a b) : q ++ [b] < p ++ [a] := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => exact List.Lex.rel h
      | cons c cs => exact List.Lex.rel h
  | cons c cs ih =>
      cases q with
      | nil => exact List.Lex.rel h
      | cons d ds =>
          by_cases hcd : c = d
          · subst d
            exact List.Lex.cons (ih ds (by simpa [route] using h))
          · exact List.Lex.rel (by simpa [route, hcd, Routing.Greater] using h)

theorem route_coordinates_iff (p q : List K) : route p q = .coordinates ↔ p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp [route]
  | cons c cs ih =>
      cases q with
      | nil => simp [route]
      | cons d ds =>
          by_cases hcd : c = d
          · subst d
            simp [route, ih]
          · simp [route, hcd]

theorem route_anchors_distinct (p q : List K) {c d : K}
    (h : route p q = .anchors c d) : c ≠ d := by
  induction p generalizing q with
  | nil => cases q <;> simp [route] at h
  | cons a as ih =>
      cases q with
      | nil => simp [route] at h
      | cons b bs =>
          by_cases hab : a = b
          · exact ih bs (by simpa [route, hab] using h)
          · simp only [route, if_neg hab, Routing.anchors.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact hab

def addArc (D : System (Fin n) K) (x y : Fin n) : System (Fin n) K :=
  { D with edge := fun a b => D.edge a b || decide (a = x ∧ b = y) }

def boundBelow (D : System (Fin n) K) (x : Fin n) (c : K) : System (Fin n) K :=
  { D with upper := Function.update D.upper x (min (D.upper x) c) }

def boundAbove (D : System (Fin n) K) (x : Fin n) (c : K) : System (Fin n) K :=
  { D with lower := Function.update D.lower x (max (D.lower x) c) }

theorem addArc_feasible_iff (D : System (Fin n) K) (x y : Fin n) (X : Fin n → K) :
    (addArc D x y).StrictlyFeasible X ↔ D.StrictlyFeasible X ∧ X x < X y := by
  constructor
  · intro h
    exact ⟨⟨h.1, fun a b hab => h.2 a b (by simp [addArc, hab])⟩,
      h.2 x y (by simp [addArc])⟩
  · rintro ⟨h, hxy⟩
    refine ⟨h.1, ?_⟩
    intro a b hab
    have hh : D.edge a b = true ∨ (a = x ∧ b = y) := by simpa [addArc] using hab
    rcases hh with he | ⟨rfl, rfl⟩
    · exact h.2 a b he
    · exact hxy

theorem boundBelow_feasible_iff (D : System (Fin n) K) (x : Fin n) (c : K)
    (X : Fin n → K) :
    (boundBelow D x c).StrictlyFeasible X ↔ D.StrictlyFeasible X ∧ X x < c := by
  constructor
  · intro h
    have hx : X x < min (D.upper x) c := by simpa [boundBelow] using (h.1 x).2
    refine ⟨⟨?_, h.2⟩, (lt_min_iff.mp hx).2⟩
    intro y
    by_cases hy : y = x
    · subst y
      exact ⟨(h.1 x).1, (lt_min_iff.mp hx).1⟩
    · simpa [boundBelow, Function.update_of_ne hy] using h.1 y
  · rintro ⟨h, hc⟩
    refine ⟨?_, h.2⟩
    intro y
    by_cases hy : y = x
    · subst y
      simpa [boundBelow] using And.intro (h.1 x).1 (lt_min (h.1 x).2 hc)
    · simpa [boundBelow, Function.update_of_ne hy] using h.1 y

theorem boundAbove_feasible_iff (D : System (Fin n) K) (x : Fin n) (c : K)
    (X : Fin n → K) :
    (boundAbove D x c).StrictlyFeasible X ↔ D.StrictlyFeasible X ∧ c < X x := by
  constructor
  · intro h
    have hx : max (D.lower x) c < X x := by simpa [boundAbove] using (h.1 x).1
    refine ⟨⟨?_, h.2⟩, (max_lt_iff.mp hx).2⟩
    intro y
    by_cases hy : y = x
    · subst y
      exact ⟨(max_lt_iff.mp hx).1, (h.1 x).2⟩
    · simpa [boundAbove, Function.update_of_ne hy] using h.1 y
  · rintro ⟨h, hc⟩
    refine ⟨?_, h.2⟩
    intro y
    by_cases hy : y = x
    · subst y
      simpa [boundAbove] using And.intro (max_lt (h.1 x).1 hc) (h.1 x).2
    · simpa [boundAbove, Function.update_of_ne hy] using h.1 y

/-- Record the literal local comparison. Different child anchors require no
new graph constraint because their order is already fixed. -/
def recordSystem (D : System (Fin n) K) (r : Routing K) (x y : Fin n)
    (answer : Answer) : System (Fin n) K :=
  match r, answer with
  | .coordinates, .less => addArc D x y
  | .coordinates, .greater => addArc D y x
  | .leftFree c, .less => boundBelow D x c
  | .leftFree c, .greater => boundAbove D x c
  | .rightFree c, .less => boundAbove D y c
  | .rightFree c, .greater => boundBelow D y c
  | .anchors _ _, _ => D

def record (s : State n K) (q : Query n) (answer : Answer) : State n K :=
  { s with system := (recordSystem s.system
      (route (s.location q.left) (s.location q.right)) q.left q.right answer) }

/-- The fixed-anchor branch must return its already determined order. -/
def Routing.AnchorAnswer (r : Routing K) (answer : Answer) : Prop :=
  match r with
  | .anchors c d => match answer with
      | .less => c < d
      | .greater => d < c
  | _ => True

theorem recordSystem_feasible_iff (D : System (Fin n) K) (r : Routing K)
    (x y : Fin n) (answer : Answer) (hr : r.AnchorAnswer answer) (X : Fin n → K) :
    (recordSystem D r x y answer).StrictlyFeasible X ↔
      D.StrictlyFeasible X ∧ r.Holds (X x) (X y) answer := by
  cases r <;> cases answer <;>
    simp_all only [recordSystem, Routing.AnchorAnswer, Routing.Holds, Routing.Less,
      Routing.Greater, addArc_feasible_iff, boundBelow_feasible_iff,
      boundAbove_feasible_iff, and_true]

theorem record_consistent (s : State n K) (history : History n)
    (hs : s.Consistent history) (q : Query n) (answer : Answer)
    (hr : (route (s.location q.left) (s.location q.right)).AnchorAnswer answer) :
    (record s q answer).Consistent (⟨q, answer⟩ :: history) := by
  intro X hX o ho
  have hparts := (recordSystem_feasible_iff s.system _ q.left q.right answer hr X).mp hX
  rcases List.mem_cons.mp ho with rfl | ho
  · cases answer with
    | less => exact route_less_sound _ _ _ _ hparts.2
    | greater => exact route_greater_sound _ _ _ _ hparts.2
  · exact hs X hparts.1 o ho

theorem record_localArcs (s : State n K) (hs : s.LocalArcs)
    (q : Query n) (answer : Answer) : (record s q answer).LocalArcs := by
  intro x y hxy
  have hr := route_coordinates_iff (s.location q.left) (s.location q.right)
  cases heq : route (s.location q.left) (s.location q.right) with
  | coordinates =>
      have hloc := hr.mp heq
      cases answer with
      | less =>
          have h : s.system.edge x y = true ∨ (x = q.left ∧ y = q.right) := by
            simpa [record, heq, recordSystem, addArc] using hxy
          rcases h with h | ⟨rfl, rfl⟩
          · exact hs x y h
          · exact hloc
      | greater =>
          have h : s.system.edge x y = true ∨ (x = q.right ∧ y = q.left) := by
            simpa [record, heq, recordSystem, addArc] using hxy
          rcases h with h | ⟨rfl, rfl⟩
          · exact hs x y h
          · exact hloc.symm
  | leftFree c =>
      apply hs x y
      cases answer <;> simpa [record, heq, recordSystem, boundBelow, boundAbove] using hxy
  | rightFree c =>
      apply hs x y
      cases answer <;> simpa [record, heq, recordSystem, boundBelow, boundAbove] using hxy
  | anchors c d =>
      apply hs x y
      cases answer <;> simpa [record, heq, recordSystem] using hxy

end OrderedField

open MeasureTheory Set

theorem routingEvent_measurable {n : ℕ} (r : Routing ℝ) (x y : Fin n) (answer : Answer) :
    MeasurableSet {X : Fin n → ℝ | r.Holds (X x) (X y) answer} := by
  cases r <;> cases answer <;>
    simp only [Routing.Holds, Routing.Less, Routing.Greater]
  all_goals first
    | exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)
    | exact measurableSet_lt (measurable_pi_apply _) measurable_const
    | exact measurableSet_lt measurable_const (measurable_pi_apply _)
    | exact MeasurableSet.const _

theorem record_region {n : ℕ} (s : State n ℝ) (q : Query n) (answer : Answer)
    (hr : (route (s.location q.left) (s.location q.right)).AnchorAnswer answer) :
    region (record s q answer).system =
      {X | (route (s.location q.left) (s.location q.right)).Holds
        (X q.left) (X q.right) answer} ∩ region s.system := by
  ext X
  exact (recordSystem_feasible_iff s.system _ q.left q.right answer hr X).trans and_comm

/-- A certified local probability is exactly the retained-volume fraction of
the actual recorded state. -/
theorem record_volume_retention {n : ℕ} (s : State n ℝ) (q : Query n) (answer : Answer)
    (hr : (route (s.location q.left) (s.location q.right)).AnchorAnswer answer)
    (hV : 0 < nodeVolume s.system) (r : ℝ)
    (hprob : r ≤ (uniformMeasure s.system).real
      {X | (route (s.location q.left) (s.location q.right)).Holds
        (X q.left) (X q.right) answer}) :
    r * nodeVolume s.system ≤ nodeVolume (record s q answer).system :=
  retained_volume s.system (record s q answer).system _ r
    (routingEvent_measurable _ _ _ _) (record_region s q answer hr) hV hprob

end SortingAdversary.Continuous.TreeState
